module FJ.Syntax.Absfj_syntax where

-- Haskell module generated by the BNF converter


newtype Id = Id String deriving (Eq,Ord,Show)

data Program =
   CProgram [ClassDecl] Exp
  deriving (Eq,Ord,Show)

data ClassDecl =
   CDecl Id ClassName [FieldDecl] Constructor [MethodDecl]
  deriving (Eq,Ord,Show)

data FieldDecl =
   FDecl ClassName Id
  deriving (Eq,Ord,Show)

data Constructor =
   KDecl Id [Field] [Arg] [Assignment]
  deriving (Eq,Ord,Show)

data Field =
   Field ClassName Id
  deriving (Eq,Ord,Show)

data FormalArg =
   FormalArg ClassName
  deriving (Eq,Ord,Show)

data Arg =
   Arg Id
  deriving (Eq,Ord,Show)

data Assignment =
   Assignment Id Id
  deriving (Eq,Ord,Show)

data MethodDecl =
   MethodDecl ClassName Id [FormalArg] Term
  deriving (Eq,Ord,Show)

data Term =
   TermVar Id
 | TermFieldAccess Term Id
 | TermMethodInvoc Term Id [Term]
 | TermExp Exp
  deriving (Eq,Ord,Show)

data Exp =
   CastExp ClassName Term
 | NewExp Id [Term]
  deriving (Eq,Ord,Show)

data ClassName =
   ClassObject
 | ClassId Id
  deriving (Eq,Ord,Show)

