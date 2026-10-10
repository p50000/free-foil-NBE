{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
-- | Template Haskell that generates a monomorphic NbE for one language. From
-- the signature and the binder type that free-foil's @mkFreeFoil@ generates,
-- 'mkValue' generates a value type with one constructor per signature
-- constructor, together with its evaluation and readback. A value is then one
-- heap object, where a 'FreeFoil.NbE.Value' is a constructor around a
-- signature cell. As with 'FreeFoil.NbE.Eval', the language writes only its
-- elimination rules.
--
-- The generated code follows the hand-written @LambdaPi.Monomorphic@
-- constructor by constructor, and its semantic domain is that of
-- "FreeFoil.NbE": term positions hold values, and a node with scoped positions
-- is suspended whole under one environment. The generator follows free-foil's
-- Template Haskell (Kudasov, Shakirova, Shalagin and Tyulebaeva, /Free Foil:
-- Generating Efficient and Scope-Safe Abstract Syntax/, 2024): it reifies the
-- signature and emits one clause per constructor, as @mkFreeFoil@ does for
-- its 'Foil.CoSinkable' instances.
module FreeFoil.NbE.TH
  ( -- * Configuration
    ValueConfig (..)
  , defaultValueConfig
    -- * Generation
  , mkValue
  ) where

import           Control.Monad              (forM, unless)
import qualified Control.Monad.Foil         as Foil
import           Control.Monad.Free.Foil    (AST (..), ScopedAST (..))
import           Data.List                  (isSuffixOf)
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (addModFinalizer)

-- * Configuration

-- | Names of the generated declarations and the language they are for.
data ValueConfig = ValueConfig
  { valueSignature :: Name
    -- ^ The signature bifunctor, e.g. @''TermSig@. Its last two type
    -- parameters are the scoped and the term positions.
  , valueBinder :: Name
    -- ^ The binder (pattern) type of the syntax, e.g. @''FFPattern@.
  , valueTypeName :: String
    -- ^ The value type.
  , valueVarConName :: String
    -- ^ The constructor of neutral variables.
  , valueConNameModifier :: String -> String
    -- ^ The value constructor for a signature constructor.
  , valueEvalName :: String
    -- ^ Evaluation, @Substitution V i o -> AST binder sig i -> V o@.
  , valueEvalNodeName :: String
    -- ^ The default evaluation of a node, which treats every constructor as
    -- an introduction form.
  , valueEvalSigName :: Maybe String
    -- ^ The language's evaluation of a node, written by hand next to the
    -- splice, with the type
    -- @Substitution V i o -> sig (ScopedAST binder sig i) (AST binder sig i) -> V o@.
    -- It implements the elimination rules and falls back to the default for
    -- the other nodes. The splice marks it @INLINE@, so that it compiles into
    -- one loop with evaluation. 'Nothing' means that the language has no
    -- elimination rules, and evaluation uses the default for every node.
  , valueQuoteName :: String
    -- ^ Readback, @Distinct n => Scope n -> V n -> AST binder sig n@. Its
    -- helper for scoped positions gets the suffix @Scoped@.
  , valueNfName :: String
    -- ^ Normalisation, @Distinct n => Scope n -> AST binder sig n -> AST binder sig n@.
  , valueUnpackBinder :: Bool
    -- ^ Whether to store the binder of a scoped position as an unpacked
    -- 'Foil.NameBinder' when the binder type has a single constructor with a
    -- single 'Foil.NameBinder' field. Otherwise, values store the whole
    -- pattern, as they do for any other binder type.
  }

-- | The configuration for a signature and a binder type: the value type
-- @Val@ with constructors @VVar@ and, for a signature constructor @FooSig@,
-- @VFoo@; the functions @eval@, @evalNode@, @quote@ and @nf@; and the
-- language's own @evalSig@. Binders are unpacked where possible.
defaultValueConfig :: Name -> Name -> ValueConfig
defaultValueConfig sig binder = ValueConfig
  { valueSignature = sig
  , valueBinder = binder
  , valueTypeName = "Val"
  , valueVarConName = "VVar"
  , valueConNameModifier = \con -> 'V' : dropSuffix "Sig" con
  , valueEvalName = "eval"
  , valueEvalNodeName = "evalNode"
  , valueEvalSigName = Just "evalSig"
  , valueQuoteName = "quote"
  , valueNfName = "nf"
  , valueUnpackBinder = True
  }
  where
    dropSuffix suffix s
      | suffix `isSuffixOf` s = take (length s - length suffix) s
      | otherwise = s

-- * Generation

-- | How a value constructor stores the binder of a scoped position.
data BinderRep
  = UnpackedNameBinder Name
    -- ^ The binder type has a single constructor (named here) with a single
    -- 'Foil.NameBinder' field, so the value stores that field unpacked and
    -- readback refreshes it with 'Foil.withRefreshed'.
  | WholePattern
    -- ^ Any other binder type: the value stores the pattern, and readback
    -- refreshes it with 'Foil.withRefreshedPattern'.

-- | A field of a signature constructor.
data Field
  = FieldTerm
  | FieldScoped
  | FieldPayload BangType

-- | A signature constructor with its classified fields.
data SigCon = SigCon
  { sigConName :: Name
  , sigConFields :: [Field]
  }

-- | Generate the value type of a language and its normaliser:
--
-- * the value type: a neutral variable, and one constructor per signature
--   constructor, which holds term positions as (lazy) values and, if the
--   node has scoped positions, the captured environment followed by each
--   scoped position's binder and body;
-- * its 'Foil.InjectName' and 'Foil.Sinkable' instances;
-- * evaluation, which looks variables up and hands nodes to the language's
--   rules (see 'valueEvalSigName'), and the default evaluation of a node;
-- * readback, which refreshes each binder of a suspended node and evaluates
--   its body once, and normalisation.
--
-- The splice needs the extensions @BangPatterns@, @DataKinds@, @GADTs@,
-- @KindSignatures@, @LambdaCase@ and @RankNTypes@. Every field of a signature
-- constructor must be the scoped parameter, the term parameter, or a type
-- without type variables, and the signature must have no other parameters.
mkValue :: ValueConfig -> Q [Dec]
mkValue ValueConfig{..} = do
  sigCons <- reifySignature valueSignature
  binderRep <- if valueUnpackBinder then reifyBinder valueBinder else return WholePattern

  let valT = mkName valueTypeName
      varCon = mkName valueVarConName
      evalN = mkName valueEvalName
      evalNodeN = mkName valueEvalNodeName
      quoteN = mkName valueQuoteName
      quoteScopedN = mkName (valueQuoteName ++ "Scoped")
      nfN = mkName valueNfName
      conOf c = mkName (valueConNameModifier (nameBase (sigConName c)))

      hasScoped c = any isScoped (sigConFields c)
      anyScoped = any hasScoped sigCons

      valueOf n = ConT valT `AppT` n
      astOf n = ConT ''AST `AppT` ConT valueBinder `AppT` ConT valueSignature `AppT` n
      scopedOf n = ConT ''ScopedAST `AppT` ConT valueBinder `AppT` ConT valueSignature `AppT` n
      substOf i o = ConT ''Foil.Substitution `AppT` ConT valT `AppT` i `AppT` o
      nodeOf i = ConT valueSignature `AppT` scopedOf i `AppT` astOf i
      binderOf i l = case binderRep of
        UnpackedNameBinder _ -> ConT ''Foil.NameBinder `AppT` i `AppT` l
        WholePattern -> ConT valueBinder `AppT` i `AppT` l
      kindedS v = KindedTV v SpecifiedSpec (ConT ''Foil.S)
      forallS vs ctx t = ForallT (map kindedS vs) ctx t
      distinct n = ConT ''Foil.Distinct `AppT` n
      lazy = Bang NoSourceUnpackedness NoSourceStrictness
      strict = Bang NoSourceUnpackedness SourceStrict
      binderBang = case binderRep of
        UnpackedNameBinder _ -> Bang SourceUnpack SourceStrict
        WholePattern -> strict

  -- The value type.
  dataN <- newName "n"
  varConDecl <- do
    n <- newName "n"
    return $ ForallC [kindedS n] []
      (GadtC [varCon] [(Bang SourceUnpack SourceStrict, ConT ''Foil.Name `AppT` VarT n)] (valueOf (VarT n)))
  valueCons <- forM sigCons $ \c -> do
    n <- newName "n"
    i <- newName "i"
    (ls, fields) <- fmap unzip $ forM (sigConFields c) $ \case
      FieldTerm -> return ([], [(lazy, valueOf (VarT n))])
      FieldPayload bt -> return ([], [bt])
      FieldScoped -> do
        l <- newName "l"
        return ([l], [(binderBang, binderOf (VarT i) (VarT l)), (lazy, astOf (VarT l))])
    let env = [ (strict, substOf (VarT i) (VarT n)) | hasScoped c ]
        tvs = [ i | hasScoped c ] ++ concat ls ++ [n]
    return $ ForallC (map kindedS tvs) [] (GadtC [conOf c] (env ++ concat fields) (valueOf (VarT n)))
  let dataDecl = DataD [] valT [KindedTV dataN BndrReq (ConT ''Foil.S)] Nothing (varConDecl : valueCons) []

  -- InjectName and Sinkable.
  let injectDecl =
        InstanceD Nothing [] (ConT ''Foil.InjectName `AppT` ConT valT)
          [ValD (VarP 'Foil.injectName) (NormalB (ConE varCon)) []]
  sinkDecl <- do
    rename <- newName "rename"
    x <- newName "x"
    let sinkE e = VarE 'Foil.sinkabilityProof `AppE` VarE rename `AppE` e
        varMatch = Match (ConP varCon [] [VarP x]) (NormalB (ConE varCon `AppE` (VarE rename `AppE` VarE x))) []
    matches <- forM sigCons $ \c -> do
      env <- newName "env"
      vars <- fieldVars (sigConFields c)
      let args = flip concatMap vars $ \case
            TermVar v -> [sinkE (VarE v)]
            PayloadVar v -> [VarE v]
            ScopedVars b body -> [VarE b, VarE body]
          envPat = [ VarP env | hasScoped c ]
          envArg = [ sinkE (VarE env) | hasScoped c ]
      return $ Match (ConP (conOf c) [] (envPat ++ valuePats vars))
        (NormalB (foldl AppE (ConE (conOf c)) (envArg ++ args))) []
    return $ InstanceD Nothing [] (ConT ''Foil.Sinkable `AppT` ConT valT)
      [FunD 'Foil.sinkabilityProof [Clause [VarP rename] (NormalB (LamCaseE (varMatch : matches))) []]]

  -- The default evaluation of a node.
  evalNodeDecls <- do
    i <- newName "i"
    o <- newName "o"
    let envUsed = any (\c -> hasScoped c || any isTerm (sigConFields c)) sigCons
    env <- newName (if envUsed then "env" else "_env")
    matches <- forM sigCons $ \c -> do
      vars <- fieldVars (sigConFields c)
      -- One pattern per signature field. A scoped field gives two arguments
      -- of the value constructor, its binder and its body.
      let pats = flip map vars $ \case
            TermVar v -> VarP v
            PayloadVar v -> VarP v
            ScopedVars b body -> ConP 'ScopedAST [] [binderPat b, VarP body]
          binderPat b = case binderRep of
            UnpackedNameBinder patCon -> ConP patCon [] [VarP b]
            WholePattern -> VarP b
          args = flip concatMap vars $ \case
            TermVar v -> [VarE evalN `AppE` VarE env `AppE` VarE v]
            PayloadVar v -> [VarE v]
            ScopedVars b body -> [VarE b, VarE body]
          envArg = [ VarE env | hasScoped c ]
      return $ Match (ConP (sigConName c) [] pats)
        (NormalB (foldl AppE (ConE (conOf c)) (envArg ++ args))) []
    return
      [ SigD evalNodeN (forallS [i, o] [] (substOf (VarT i) (VarT o) `arrow` nodeOf (VarT i) `arrow` valueOf (VarT o)))
      , PragmaD (InlineP evalNodeN Inline FunLike AllPhases)
      , FunD evalNodeN [Clause [VarP env] (NormalB (LamCaseE matches)) []]
      ]

  -- Evaluation. The language's evaluation of nodes is marked INLINE, so
  -- that GHC chooses 'eval' as the loop breaker of the two and compiles them
  -- into one loop, as in a hand-written evaluator.
  evalDecls <- do
    i <- newName "i"
    o <- newName "o"
    env <- newName "env"
    x <- newName "x"
    node <- newName "node"
    let evalSigN = maybe evalNodeN mkName valueEvalSigName
    return $
      [ SigD evalN (forallS [i, o] [] (substOf (VarT i) (VarT o) `arrow` astOf (VarT i) `arrow` valueOf (VarT o)))
      , FunD evalN [Clause [BangP (VarP env)] (NormalB (LamCaseE
          [ Match (ConP 'Var [] [VarP x]) (NormalB (VarE 'Foil.lookupSubst `AppE` VarE env `AppE` VarE x)) []
          , Match (ConP 'Node [] [VarP node]) (NormalB (VarE evalSigN `AppE` VarE env `AppE` VarE node)) []
          ])) []]
      ] ++
      [ PragmaD (InlineP (mkName name) Inline FunLike AllPhases) | Just name <- [valueEvalSigName] ]

  -- Readback.
  quoteDecls <- do
    n <- newName "n"
    scope <- newName "scope"
    x <- newName "x"
    let quoteE e = VarE quoteN `AppE` VarE scope `AppE` e
    matches <- forM sigCons $ \c -> do
      env <- newName "env"
      vars <- fieldVars (sigConFields c)
      -- One argument per signature field. A scoped field matches two fields
      -- of the value constructor, its binder and its body.
      let args = flip map vars $ \case
            TermVar v -> quoteE (VarE v)
            PayloadVar v -> VarE v
            ScopedVars b body ->
              VarE quoteScopedN `AppE` VarE scope `AppE` VarE env `AppE` VarE b `AppE` VarE body
          envPat = [ VarP env | hasScoped c ]
      return $ Match (ConP (conOf c) [] (envPat ++ valuePats vars))
        (NormalB (ConE 'Node `AppE` foldl AppE (ConE (sigConName c)) args)) []
    let varMatch = Match (ConP varCon [] [VarP x]) (NormalB (ConE 'Var `AppE` VarE x)) []
    return
      [ SigD quoteN (forallS [n] [distinct (VarT n)] (ConT ''Foil.Scope `AppT` VarT n `arrow` valueOf (VarT n) `arrow` astOf (VarT n)))
      , FunD quoteN [Clause [VarP scope] (NormalB (LamCaseE (varMatch : matches))) []]
      ]

  -- Readback of one scoped position: refresh the binder, extend the captured
  -- environment with a renaming to the fresh name, evaluate the body once and
  -- read it back.
  quoteScopedDecls <- if not anyScoped then return [] else do
    n <- newName "n"
    i <- newName "i"
    l <- newName "l"
    scope <- newName "scope"
    env <- newName "env"
    b <- newName "binder"
    body <- newName "body"
    b' <- newName "binder'"
    scope' <- newName "scope'"
    env' <- newName "env'"
    extendEnv <- newName "extendEnv"
    let quoteBody s e = VarE quoteN `AppE` VarE s `AppE` (VarE evalN `AppE` e `AppE` VarE body)
        rhs = case binderRep of
          UnpackedNameBinder patCon ->
            VarE 'Foil.withRefreshed `AppE` VarE scope `AppE` (VarE 'Foil.nameOf `AppE` VarE b) `AppE`
              LamE [VarP b']
                (LetE
                  [ ValD (VarP scope') (NormalB (VarE 'Foil.extendScope `AppE` VarE b' `AppE` VarE scope)) []
                  , ValD (VarP env') (NormalB (VarE 'Foil.addRename
                      `AppE` (VarE 'Foil.sink `AppE` VarE env) `AppE` VarE b `AppE` (VarE 'Foil.nameOf `AppE` VarE b'))) []
                  ]
                  (ConE 'ScopedAST `AppE` (ConE patCon `AppE` VarE b') `AppE` quoteBody scope' (VarE env')))
          WholePattern ->
            VarE 'Foil.withRefreshedPattern `AppE` VarE scope `AppE` VarE b `AppE`
              LamE [VarP extendEnv, VarP b', VarP scope']
                (ConE 'ScopedAST `AppE` VarE b' `AppE` quoteBody scope' (VarE extendEnv `AppE` VarE env))
    return
      [ SigD quoteScopedN (forallS [n, i, l] [distinct (VarT n)]
          (ConT ''Foil.Scope `AppT` VarT n `arrow` substOf (VarT i) (VarT n)
            `arrow` binderOf (VarT i) (VarT l) `arrow` astOf (VarT l) `arrow` scopedOf (VarT n)))
      , FunD quoteScopedN [Clause [VarP scope, VarP env, VarP b, VarP body] (NormalB rhs) []]
      ]

  -- Normalisation.
  nfDecls <- do
    n <- newName "n"
    scope <- newName "scope"
    return
      [ SigD nfN (forallS [n] [distinct (VarT n)] (ConT ''Foil.Scope `AppT` VarT n `arrow` astOf (VarT n) `arrow` astOf (VarT n)))
      , FunD nfN [Clause [VarP scope] (NormalB (InfixE (Just (VarE quoteN `AppE` VarE scope)) (VarE '(.))
          (Just (VarE evalN `AppE` VarE 'Foil.identitySubst)))) []]
      ]

  let generated = "/Generated/ with '" ++ show 'mkValue ++ "'. "
  addModFinalizer $ putDoc (DeclDoc valT) $ generated
    ++ "Values of '" ++ show valueSignature ++ "', one constructor per signature constructor."
  addModFinalizer $ putDoc (DeclDoc evalN) $ generated
    ++ "Evaluate a term under an environment that maps its free variables to values."
  addModFinalizer $ putDoc (DeclDoc evalNodeN) $ generated
    ++ "Evaluate a node as an introduction form: evaluate its term positions and suspend its scoped positions."
  addModFinalizer $ putDoc (DeclDoc quoteN) $ generated
    ++ "Read a value back into a term in normal form."
  addModFinalizer $ putDoc (DeclDoc nfN) $ generated
    ++ "Normal form by evaluation and readback."

  return $ concat
    [ [dataDecl, injectDecl, sinkDecl]
    , evalDecls
    , evalNodeDecls
    , quoteDecls
    , quoteScopedDecls
    , nfDecls
    ]

isScoped :: Field -> Bool
isScoped FieldScoped = True
isScoped _ = False

isTerm :: Field -> Bool
isTerm FieldTerm = True
isTerm _ = False

-- | The pattern variables of one field of a signature constructor, numbered
-- by the field's position so that the generated code reads well in
-- @-ddump-splices@.
data FieldVars
  = TermVar Name
  | PayloadVar Name
  | ScopedVars Name Name
    -- ^ The binder and the body of a scoped field.

fieldVars :: [Field] -> Q [FieldVars]
fieldVars fields = forM (zip [1 :: Int ..] fields) $ \(k, f) -> case f of
  FieldTerm -> TermVar <$> newName ("x" ++ show k)
  FieldPayload _ -> PayloadVar <$> newName ("x" ++ show k)
  FieldScoped -> ScopedVars <$> newName ("binder" ++ show k) <*> newName ("body" ++ show k)

-- | The patterns for the fields of a value constructor, after its environment.
valuePats :: [FieldVars] -> [Pat]
valuePats = concatMap $ \case
  TermVar v -> [VarP v]
  PayloadVar v -> [VarP v]
  ScopedVars b body -> [VarP b, VarP body]

arrow :: Type -> Type -> Type
arrow a b = ArrowT `AppT` a `AppT` b
infixr 1 `arrow`

-- * Reification

-- | The constructors of a signature with their fields classified.
reifySignature :: Name -> Q [SigCon]
reifySignature sig = do
  (tvars, cons) <- reifyDataType sig
  case map tvName tvars of
    [scopeTv, termTv] -> concat <$> mapM (sigCon scopeTv termTv) cons
    _ -> fail $ "mkValue: the signature " ++ show sig
      ++ " must have exactly two type parameters (scoped and term positions)"
  where
    sigCon scopeTv termTv = \case
      NormalC name bts -> pure <$> classify name scopeTv termTv bts
      RecC name vbts -> pure <$> classify name scopeTv termTv [ (b, t) | (_, b, t) <- vbts ]
      InfixC l name r -> pure <$> classify name scopeTv termTv [l, r]
      ForallC _ _ con -> sigCon scopeTv termTv con
      GadtC names bts ret -> do
        (s, t) <- gadtParams ret
        mapM (\name -> classify name s t bts) names
      RecGadtC names vbts ret -> do
        (s, t) <- gadtParams ret
        mapM (\name -> classify name s t [ (b, ty) | (_, b, ty) <- vbts ]) names

    gadtParams = \case
      AppT (AppT (ConT _) (VarT s)) (VarT t) -> return (s, t)
      ret -> fail ("mkValue: unexpected return type of a signature constructor: " ++ pprint ret)

    classify name s t bts = SigCon name <$> mapM (field name s t) bts

    field name s t (bang_, ty) = case ty of
      VarT v | v == s -> return FieldScoped
             | v == t -> return FieldTerm
      _ -> do
        unless (null (typeVars ty)) $ fail $
          "mkValue: unsupported field type " ++ pprint ty ++ " in " ++ show name
          ++ " (a field must be the scoped parameter, the term parameter, or a type without type variables)"
        return (FieldPayload (bang_, ty))

-- | How the binder type is stored in values.
reifyBinder :: Name -> Q BinderRep
reifyBinder binder = do
  (tvars, cons) <- reifyDataType binder
  case (map tvName tvars, cons) of
    ([n, l], [con]) | Just patCon <- singleNameBinder n l con -> return (UnpackedNameBinder patCon)
    ([_, _], _) -> return WholePattern
    _ -> fail $ "mkValue: the binder type " ++ show binder
      ++ " must have exactly two (scope) type parameters"
  where
    -- A constructor whose only field is a 'Foil.NameBinder' between the same
    -- two scopes as the pattern.
    singleNameBinder n l = \case
      ForallC _ _ con -> singleNameBinder n l con
      GadtC [name] [(_, AppT (AppT (ConT nb) (VarT a)) (VarT b))] (AppT (AppT (ConT _) (VarT a')) (VarT b'))
        | nb == ''Foil.NameBinder, a == a', b == b' -> Just name
      NormalC name [(_, AppT (AppT (ConT nb) (VarT a)) (VarT b))]
        | nb == ''Foil.NameBinder, a == n, b == l -> Just name
      _ -> Nothing

reifyDataType :: Name -> Q ([TyVarBndr ()], [Con])
reifyDataType name = reify name >>= \case
  TyConI (DataD _ _ tvars _ cons _) -> return (map (() <$) tvars, cons)
  TyConI (NewtypeD _ _ tvars _ con _) -> return (map (() <$) tvars, [con])
  info -> fail ("mkValue: " ++ show name ++ " is not a data type: " ++ pprint info)

tvName :: TyVarBndr flag -> Name
tvName = \case
  PlainTV n _ -> n
  KindedTV n _ _ -> n

-- | The type variables that occur in a type.
typeVars :: Type -> [Name]
typeVars = \case
  VarT v -> [v]
  AppT a b -> typeVars a ++ typeVars b
  AppKindT a _ -> typeVars a
  SigT a _ -> typeVars a
  ParensT a -> typeVars a
  InfixT a _ b -> typeVars a ++ typeVars b
  UInfixT a _ b -> typeVars a ++ typeVars b
  ForallT _ _ a -> typeVars a
  _ -> []
