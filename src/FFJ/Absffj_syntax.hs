module FFJ.Absffj_syntax where

-- Haskell module generated by the BNF converter


newtype Id = Id String deriving (Eq,Ord,Show)
data CDList =
   CDList [CDef] Exp
  deriving (Eq,Ord,Show)

data CDef =
   CDDecl CD
 | CDRef CR
  deriving (Eq,Ord,Show)

data CD =
   CDecl Id Type [FD] KD [MD]
  deriving (Eq,Ord,Show)

data CR =
   CRef Id [FD] KR [MD] [MR]
  deriving (Eq,Ord,Show)

data FD =
   FDecl Type Id
  deriving (Eq,Ord,Show)

data KD =
   KDecl Id [Field] [Arg] [Assignment]
  deriving (Eq,Ord,Show)

data KR =
   KRef Id [Field] [Arg] [Assignment]
  deriving (Eq,Ord,Show)

data Field =
   Field Type Id
  deriving (Eq,Ord,Show)

data FormalArg =
   FormalArg Type Id
  deriving (Eq,Ord,Show)

data Arg =
   Arg Id
  deriving (Eq,Ord,Show)

data Assignment =
   Assignment Id Id
  deriving (Eq,Ord,Show)

data MD =
   MethodDecl Type Id [FormalArg] Term
  deriving (Eq,Ord,Show)

data MR =
   MethodRef Id Id [FormalArg] Term
  deriving (Eq,Ord,Show)

data Type =
   TypeObject
 | TypeId Id
  deriving (Eq,Ord,Show)

data Term =
   TermVar Id
 | TermFieldAccess Term Id
 | TermMethodInvoc Term Id [Term]
 | TermExp Exp
  deriving (Eq,Ord,Show)

data Exp =
   CastExp Id Term
 | NewExp Id [Term]
  deriving (Eq,Ord,Show)
