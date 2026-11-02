-- | Example terms of the dependent types language: closed terms with their
-- types and normal forms, and pairs of terms of one type that are
-- convertible or not, all in a context of types. The examples are strings,
-- elaborated by "DependentTypes.Elaborate".
module DependentTypes.Examples
  ( Example (..)
  , unitVariable
  , unitResult
  , functionEta
  , unitFunctionEta
  , secondComponent
  , firstOfPair
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
    "\\(f : (A : U 0) -> Unit). \\(A : U 0). f A"
    "(f : (A : U 0) -> Unit) -> (A : U 0) -> Unit"
    "\\(f : (A : U 0) -> Unit). \\(A : U 0). tt"

-- | A variable of a function type that is not a singleton stays as it is:
-- η for functions goes by shape, in conversion.
functionEta :: Example
functionEta =
  Example
    "\\(A : U 0). \\(f : (x : A) -> A). f"
    "(A : U 0) -> (f : (x : A) -> A) -> (x : A) -> A"
    "\\(A : U 0). \\(f : (x : A) -> A). f"

-- | A function into the unit type is constant: its type is a singleton, so
-- @f@ becomes @\\(x : Unit). tt@.
unitFunctionEta :: Example
unitFunctionEta =
  Example
    "\\(f : (x : Unit) -> Unit). f"
    "(f : (x : Unit) -> Unit) -> (x : Unit) -> Unit"
    "\\(f : (x : Unit) -> Unit). \\(x : Unit). tt"

-- | The second component of a neutral pair has the type of the codomain at
-- the first, here @(\\(z : A). Unit) (first p)@, which is @Unit@.
secondComponent :: Example
secondComponent =
  Example
    "\\(A : U 0). \\(p : (a : A) * ((\\(z : A). Unit) a)). second p"
    "(A : U 0) -> (p : (a : A) * ((\\(z : A). Unit) a)) -> Unit"
    "\\(A : U 0). \\(p : (a : A) * Unit). tt"

-- | A projection of a pair reduces.
firstOfPair :: Example
firstOfPair =
  Example
    "\\(A : U 0). \\(a : A). (\\(p : (x : A) * Unit). first p) (a, tt)"
    "(A : U 0) -> (a : A) -> A"
    "\\(A : U 0). \\(a : A). a"

-- | A redex in the type of a binder is reduced, and the name gets the
-- reduced type.
redexInDomain :: Example
redexInDomain =
  Example
    "\\(x : (\\(A : U 0). A) Unit). x"
    "(x : Unit) -> Unit"
    "\\(x : Unit). tt"

-- | The examples with their names.
examples :: [(String, Example)]
examples =
  [ ("unitVariable",    unitVariable)
  , ("unitResult",      unitResult)
  , ("functionEta",     functionEta)
  , ("unitFunctionEta", unitFunctionEta)
  , ("secondComponent", secondComponent)
  , ("firstOfPair",     firstOfPair)
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
        "(A : U 0) -> (f : (x : A) -> A) -> (x : A) -> A"
        "\\(A : U 0). \\(f : (x : A) -> A). f"
        "\\(A : U 0). \\(f : (x : A) -> A). \\(x : A). f x"
        True )
  , ( "two variables of the unit type"
    , Conversion "(x : Unit) -> (y : Unit) -> Unit" "\\(x : Unit). \\(y : Unit). x" "\\(x : Unit). \\(y : Unit). y" True )
  , ( "two functions into the unit type"
    , Conversion
        "(A : U 0) -> (f : (x : A) -> Unit) -> (g : (x : A) -> Unit) -> (x : A) -> Unit"
        "\\(A : U 0). \\(f : (x : A) -> Unit). \\(g : (x : A) -> Unit). f"
        "\\(A : U 0). \\(f : (x : A) -> Unit). \\(g : (x : A) -> Unit). g"
        True )
  , ( "two variables of a type variable"
    , Conversion "(A : U 0) -> (x : A) -> (y : A) -> A" "\\(A : U 0). \\(x : A). \\(y : A). x" "\\(A : U 0). \\(x : A). \\(y : A). y" False )
  , ( "a pair variable and the pair of its projections"
    , Conversion
        "(A : U 0) -> (B : (x : A) -> U 0) -> (p : (x : A) * B x) -> (x : A) * B x"
        "\\(A : U 0). \\(B : (x : A) -> U 0). \\(p : (x : A) * B x). p"
        "\\(A : U 0). \\(B : (x : A) -> U 0). \\(p : (x : A) * B x). (first p, second p)"
        True )
  , ( "a pair variable of unit components and the pair of units"
    , Conversion
        "(p : (u : Unit) * Unit) -> (u : Unit) * Unit"
        "\\(p : (u : Unit) * Unit). p"
        "\\(p : (u : Unit) * Unit). (tt, tt)"
        True )
  , ( "two pair variables of unit components"
    , Conversion
        "(p : (u : Unit) * Unit) -> (q : (u : Unit) * Unit) -> (u : Unit) * Unit"
        "\\(p : (u : Unit) * Unit). \\(q : (u : Unit) * Unit). p"
        "\\(p : (u : Unit) * Unit). \\(q : (u : Unit) * Unit). q"
        True )
  , ( "two pair variables whose first components are not of a singleton type"
    , Conversion
        "(A : U 0) -> (p : (x : A) * Unit) -> (q : (x : A) * Unit) -> (x : A) * Unit"
        "\\(A : U 0). \\(p : (x : A) * Unit). \\(q : (x : A) * Unit). p"
        "\\(A : U 0). \\(p : (x : A) * Unit). \\(q : (x : A) * Unit). q"
        False )
  , ( "a pair variable and its first component paired with tt"
    , Conversion
        "(A : U 0) -> (p : (x : A) * Unit) -> (x : A) * Unit"
        "\\(A : U 0). \\(p : (x : A) * Unit). p"
        "\\(A : U 0). \\(p : (x : A) * Unit). (first p, tt)"
        True )
  , ( "two functions whose type becomes a singleton by β"
    , Conversion
        "(A : U 0) -> (f : (y : A) -> Unit) -> (g : (y : A) -> Unit) -> (y : A) -> Unit"
        "\\(A : U 0). (\\(B : (x : A) -> U 0). \\(f : (y : A) -> B y). \\(g : (y : A) -> B y). f) (\\(x : A). Unit)"
        "\\(A : U 0). (\\(B : (x : A) -> U 0). \\(f : (y : A) -> B y). \\(g : (y : A) -> B y). g) (\\(x : A). Unit)"
        True )
  , ( "a pair variable and its components swapped"
    , Conversion
        "(A : U 0) -> (p : (x : A) * A) -> (x : A) * A"
        "\\(A : U 0). \\(p : (x : A) * A). p"
        "\\(A : U 0). \\(p : (x : A) * A). (second p, first p)"
        False )
  ]
