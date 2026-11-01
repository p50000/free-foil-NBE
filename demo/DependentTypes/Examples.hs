-- | Example terms of the dependent types language: closed terms with their types and their
-- normal forms in a context of types, and pairs of convertible and of
-- inconvertible terms of one type. The examples are strings, elaborated by
-- "DependentTypes.Elaborate".
module DependentTypes.Examples
  ( Example (..)
  , unitVariable
  , unitResult
  , functionEta
  , unitFunctionEta
  , splitComponents
  , splitOfPair
  , redexInDomain
  , examples
  , Conversion (..)
  , conversions
  ) where

-- | A closed term, its type, and its normal form in a context of types.
data Example = Example String String String

-- | A variable of the unit type is @tt@.
unitVariable :: Example
unitVariable = Example "\\(x : Unit). x" "(x : Unit) -> Unit" "\\(x : Unit). tt"

-- | A neutral application of the unit type is @tt@: its type is in its
-- annotation.
unitResult :: Example
unitResult =
  Example
    "\\(f : (A : U) -> Unit). \\(A : U). f A"
    "(f : (A : U) -> Unit) -> (A : U) -> Unit"
    "\\(f : (A : U) -> Unit). \\(A : U). tt"

-- | A variable of a function type is η-expanded.
functionEta :: Example
functionEta =
  Example
    "\\(A : U). \\(f : (x : A) -> A). f"
    "(A : U) -> (f : (x : A) -> A) -> (x : A) -> A"
    "\\(A : U). \\(f : (x : A) -> A). \\(x : A). f x"

-- | The two η laws together: a function into the unit type is constant.
unitFunctionEta :: Example
unitFunctionEta =
  Example
    "\\(f : (x : Unit) -> Unit). f"
    "(f : (x : Unit) -> Unit) -> (x : Unit) -> Unit"
    "\\(f : (x : Unit) -> Unit). \\(x : Unit). tt"

-- | Under a stuck @split@, the second component has the type of the
-- codomain at the first, here @(\\(z : A). Unit) x@, which is @Unit@.
splitComponents :: Example
splitComponents =
  Example
    "\\(A : U). \\(p : (a : A) * ((\\(z : A). Unit) a)). split p : (a : A) * ((\\(z : A). Unit) a) as (x, y) in (y, y)"
    "(A : U) -> (p : (a : A) * ((\\(z : A). Unit) a)) -> (u : Unit) * Unit"
    "\\(A : U). \\(p : (a : A) * Unit). split p : (a : A) * Unit as (x, y) in (tt, tt)"

-- | A @split@ of a pair reduces.
splitOfPair :: Example
splitOfPair =
  Example
    "\\(A : U). \\(a : A). split (a, tt) : (x : A) * Unit as (x, y) in x"
    "(A : U) -> (a : A) -> A"
    "\\(A : U). \\(a : A). a"

-- | A redex in the type of a binder is reduced, and the name gets the
-- reduced type.
redexInDomain :: Example
redexInDomain =
  Example
    "\\(x : (\\(A : U). A) Unit). x"
    "(x : Unit) -> Unit"
    "\\(x : Unit). tt"

-- | The examples with their names.
examples :: [(String, Example)]
examples =
  [ ("unitVariable",    unitVariable)
  , ("unitResult",      unitResult)
  , ("functionEta",     functionEta)
  , ("unitFunctionEta", unitFunctionEta)
  , ("splitComponents", splitComponents)
  , ("splitOfPair",     splitOfPair)
  , ("redexInDomain",   redexInDomain)
  ]

-- | Two closed terms of one type, and whether they are convertible in a
-- context of types.
data Conversion = Conversion String String String Bool

-- | The conversion examples with their names.
conversions :: [(String, Conversion)]
conversions =
  [ ( "a function and its η-expansion"
    , Conversion
        "(A : U) -> (f : (x : A) -> A) -> (x : A) -> A"
        "\\(A : U). \\(f : (x : A) -> A). f"
        "\\(A : U). \\(f : (x : A) -> A). \\(x : A). f x"
        True )
  , ( "two variables of the unit type"
    , Conversion "(x : Unit) -> (y : Unit) -> Unit" "\\(x : Unit). \\(y : Unit). x" "\\(x : Unit). \\(y : Unit). y" True )
  , ( "two variables of a type variable"
    , Conversion "(A : U) -> (x : A) -> (y : A) -> A" "\\(A : U). \\(x : A). \\(y : A). x" "\\(A : U). \\(x : A). \\(y : A). y" False )
  , ( "the components of a stuck split of a unit pair"
    , Conversion
        "(p : (u : Unit) * Unit) -> (u : Unit) * Unit"
        "\\(p : (u : Unit) * Unit). split p : (u : Unit) * Unit as (x, y) in (x, y)"
        "\\(p : (u : Unit) * Unit). split p : (u : Unit) * Unit as (x, y) in (y, x)"
        True )
  ]
