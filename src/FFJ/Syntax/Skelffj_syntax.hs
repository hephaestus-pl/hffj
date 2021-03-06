module FFJ.Syntax.Skelffj_syntax where

-- Haskell module generated by the BNF converter

import FFJ.Syntax.Absffj_syntax
import FFJ.Syntax.ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

transId :: Id -> Result
transId x = case x of
  Id str  -> failure x


transCDList :: CDList -> Result
transCDList x = case x of
  CDList cdefs exp  -> failure x


transCDef :: CDef -> Result
transCDef x = case x of
  CDDecl cd  -> failure x
  CDRef cr  -> failure x


transCD :: CD -> Result
transCD x = case x of
  CDecl id type' fds kd mds  -> failure x


transCR :: CR -> Result
transCR x = case x of
  CRef id fds kr mds mrs  -> failure x


transFD :: FD -> Result
transFD x = case x of
  FDecl type' id  -> failure x


transKD :: KD -> Result
transKD x = case x of
  KDecl id fields args assignments  -> failure x


transKR :: KR -> Result
transKR x = case x of
  KRef id fields args assignments  -> failure x


transField :: Field -> Result
transField x = case x of
  Field type' id  -> failure x


transFormalArg :: FormalArg -> Result
transFormalArg x = case x of
  FormalArg type' id  -> failure x


transArg :: Arg -> Result
transArg x = case x of
  Arg id  -> failure x


transAssignment :: Assignment -> Result
transAssignment x = case x of
  Assignment id1 id2  -> failure x


transMD :: MD -> Result
transMD x = case x of
  MethodDecl type' id formalargs term  -> failure x


transMR :: MR -> Result
transMR x = case x of
  MethodRef id1 id2 formalargs3 term4  -> failure x


transType :: Type -> Result
transType x = case x of
  TypeObject  -> failure x
  TypeId id  -> failure x


transTerm :: Term -> Result
transTerm x = case x of
  TermVar id  -> failure x
  TermFieldAccess term id  -> failure x
  TermMethodInvoc term id terms  -> failure x
  TermExp exp  -> failure x


transExp :: Exp -> Result
transExp x = case x of
  CastExp type' term  -> failure x
  NewExp id terms  -> failure x



