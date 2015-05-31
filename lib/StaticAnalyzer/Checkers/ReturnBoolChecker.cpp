#include "ClangSACheckers.h"
#include "clang/AST/Attr.h"
#include "clang/AST/ParentMap.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

#include "llvm/Support/raw_os_ostream.h"

#include <iostream>

using namespace clang;
using namespace ento;

namespace {
class ReturnBoolChecker : 
    public Checker< check::PreStmt<ReturnStmt>, check::PostCall > {
  mutable std::unique_ptr<BuiltinBug> BTBad;
  mutable std::unique_ptr<BuiltinBug> BTUC;
  mutable std::set<const Stmt *> BoolFunctions;

void emitBadReport(ProgramStateRef s1, ProgramStateRef s2,
		   CheckerContext &C) const;
void emitUnderconstrainedReport(ProgramStateRef s1, ProgramStateRef s2,
				CheckerContext &C) const;
public:
  void checkPreStmt(const ReturnStmt *RS, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
//  void checkASTDecl(const FunctionDecl *D, AnalysisManager &Mgr,
//		    BugReporter &BR) const;
    };
}

void ReturnBoolChecker::emitBadReport(ProgramStateRef s1,
				      ProgramStateRef s2,
				      CheckerContext &C) const {
  ExplodedNode *N;
  if ((N = C.addTransition(s1)) && (N = C.addTransition(s2, N))) {
    if (!BTBad)
      BTBad.reset(new BuiltinBug(this, "Returns non-Boolean value"));
    C.emitReport(new BugReport(*BTBad, BTBad->getDescription(), N));
  }
}

void ReturnBoolChecker::emitUnderconstrainedReport(ProgramStateRef s1,
						   ProgramStateRef s2,
						   CheckerContext &C) const {
  ExplodedNode *N;
  if ((N = C.addTransition(s1)) && (N = C.addTransition(s2, N))) {
    if (!BTUC)
      BTUC.reset(new BuiltinBug(this,
				"Cannot sufficiently constrain return value"));
    C.emitReport(new BugReport(*BTUC, BTUC->getDescription(), N));
  }
}

/*
void ReturnBoolChecker::checkASTDecl(const FunctionDecl *D,
				     AnalysisManager &Mgr,
				     BugReporter &BR) const {
  std::cerr << "D\n";
  D->dump();
  const AttrVec &Attrs = D->getAttrs();
  if (hasSpecificAttr<ReturnsBoolAttr>(Attrs))
    BoolFunctions.insert(D->getBody());
}
*/

static const FunctionDecl *FindDecl(const Stmt *s, ASTContext &AC) {
  ArrayRef<ast_type_traits::DynTypedNode> A = AC.getParents(*s);

  //llvm::raw_os_ostream cerr(std::cerr);
  for (ast_type_traits::DynTypedNode a : A) {
    //std::cerr << "-----\n";
    //a.dump(cerr, AC.getSourceManager());
    //cerr.flush();
    const FunctionDecl *fn = a.get<FunctionDecl>();
    if (fn) {
      //std::cerr << "Found\n";
      return fn;
    }
    const Stmt *stmt = a.get<Stmt>();
    if (stmt) {
      fn = FindDecl(stmt, AC);
      if (fn) {
	//std::cerr << "Found2\n";
	return fn;
      }
    }
  }
  return nullptr;
}
  

void ReturnBoolChecker::checkPostCall(const CallEvent &Call,
				      CheckerContext &C) const {
  //std::cerr << "Call\n";
  //Call.dump();
  //std::cerr << "----\n";
  const Decl *decl = Call.getDecl();
  //decl->dump();

  const AttrVec &Attrs = decl->getAttrs();
  if (!hasSpecificAttr<ReturnsBoolAttr>(Attrs))
    return;

  //std::cerr << "Bool\n";
  
  //std::cerr << "----\n";
  QualType type = Call.getResultType();
  //type->dump();

  SValBuilder &svalBuilder = C.getSValBuilder();
  //DefinedSVal Zero = svalBuilder.makeIntVal(0, type);
  //DefinedSVal One = svalBuilder.makeIntVal(1, type);
  DefinedSVal Two = svalBuilder.makeIntVal(2, type);
  /*
  llvm::ImmutableListFactory<SVal> f;
  llvm::ImmutableList<SVal> l = f.getEmptyList();
  l = f.concat(Zero, l);
  l = f.concat(One, l);
  
  NonLoc V = svalBuilder.makeCompoundVal(type, l);
  */
  
  ProgramStateRef state = C.getState();
  //std::cerr << "----\n";
  //state->dump();

  SVal V = Call.getReturnValue();
  //std::cerr << "----\n";
  //V.dump();

  state = state->assumeInBound(V.castAs<DefinedOrUnknownSVal>(), Two, true);

  //std::cerr << "----\n";
  //V.dump();
  
  //std::cerr << "----\n";
  //state = state->BindExpr(Call.getOriginExpr(), C.getLocationContext(), isGEZero);
  //state = state->BindExpr(Call.getOriginExpr(), C.getLocationContext(), isLEOne);
  //state->dump();
  C.addTransition(state);
}

void ReturnBoolChecker::checkPreStmt(const ReturnStmt *RS,
				     CheckerContext &C) const {
  std::cerr << "RS\n";
  RS->dump();
 
  const Expr *RetE = RS->getRetValue();
  if (!RetE)
    return;

  //RetE->dump();

  ASTContext &AC = C.getASTContext();
  const FunctionDecl *fn = FindDecl(RS, AC);
  //fn->dump();

  const AttrVec &Attrs = fn->getAttrs();
  if (!hasSpecificAttr<ReturnsBoolAttr>(Attrs))
    return;
  
  //std::cerr << "BOOL!\n";
  //fn->dump();

  ProgramStateRef state = C.getState();
  std::cerr << "----\n";
  state->dump();

  SValBuilder &svalBuilder = C.getSValBuilder();

  // using getAs works less well than castAs (see t7.c).
  Optional<DefinedSVal> V = state->getSVal(RetE, C.getLocationContext())
      .castAs<DefinedSVal>();
  if (!V) {
    std::cerr << "Can't get V\n";
    return;
  }

  std::cerr << "----\nV = ";
  V->dump();
  std::cerr << '\n';
    
  // FIXME: use the same type as V throughout...
  QualType type = fn->getReturnType();
  //ASTContext &Ctx = svalBuilder.getContext();
  DefinedSVal Two = svalBuilder.makeIntVal(2, type);

  ProgramStateRef inRange = state->assumeInBound(*V, Two, true);
  ProgramStateRef outRange = state->assumeInBound(*V, Two, false);

  //std::cerr << "inRange\n";
  // BUG: this segfaults on t.c
  //inRange->dump();
  //std::cerr << "outRange\n";
  // BUG: this segfaults (on t5.c at least).
  //outRange->dump();

  std::cerr << (inRange ? "in range" : "not in range") << '\n';
  std::cerr << (outRange ? "out of range" : "not out of range") << '\n';

  // Definitely OK
  if (inRange && !outRange)
      return;

  // Definitely not OK?
  if (!inRange) {
    emitBadReport(inRange, outRange, C);
    return;
  }
  
  //std::cerr << "Can't determine correctness\n";
  emitUnderconstrainedReport(inRange, outRange, C);

  /*
  DefinedSVal Zero = svalBuilder.makeIntVal(0, Ctx.IntTy);
  DefinedSVal One = svalBuilder.makeIntVal(1, Ctx.IntTy);
  SVal isGEZero = svalBuilder.evalBinOp(state, BO_GE, *V, Zero, Ctx.IntTy);
  SVal isLEOne = svalBuilder.evalBinOp(state, BO_LE, *V, One, Ctx.IntTy);

  std::cerr << "Zero = "; Zero.dump(); std::cerr << '\n';
  std::cerr << "isGEZero = "; isGEZero.dump(); std::cerr << '\n';
  std::cerr << "One = "; One.dump(); std::cerr << '\n';
  std::cerr << "isLEOne = "; isLEOne.dump(); std::cerr << '\n';
   
  ConstraintManager &CM = state->getStateManager().getConstraintManager();
  ProgramStateRef stateGEZero, stateNotGEZero;
  std::tie(stateGEZero, stateNotGEZero) = CM.assumeDual(state, isGEZero.castAs<DefinedSVal>());

  std::cerr << (stateGEZero ? "GEZero" : "not GEZero") << '\n';
  std::cerr << (stateNotGEZero ? "NotGEZero" : "not NotGEZero") << '\n';
  */
  /*
  SVal isZero = svalBuilder.evalBinOp(state, BO_EQ, *V, Zero, Ctx.IntTy);
  SVal isOne = svalBuilder.evalBinOp(state, BO_EQ, *V, One, Ctx.IntTy);

  std::cerr << "Zero = "; Zero.dump(); std::cerr << '\n';
  std::cerr << "isZero = "; isZero.dump(); std::cerr << '\n';
  std::cerr << "One = "; One.dump(); std::cerr << '\n';
  std::cerr << "isOne = "; isOne.dump(); std::cerr << '\n';
  
  ConstraintManager &CM = state->getStateManager().getConstraintManager();

  ProgramStateRef stateZero, stateNotZero;
  std::tie(stateZero, stateNotZero) = CM.assumeDual(state, isZero.castAs<DefinedSVal>());

  std::cerr << (stateZero ? "Zero" : "not Zero") << '\n';
  std::cerr << (stateNotZero ? "NotZero" : "not NotZero") << '\n';
  
  ProgramStateRef stateOne, stateNotOne;
  std::tie(stateOne, stateNotOne) = CM.assumeDual(state, isOne.castAs<DefinedSVal>());

  std::cerr << (stateOne ? "One" : "not One") << '\n';
  std::cerr << (stateNotOne ? "NotOne" : "not NotOne") << '\n';
  
  //ExplodedNode *N = C.addTransition(stateZero);
  //N->getState()->dump();

  // Definitely 0 or 1
  if ((stateZero && !stateNotZero) || (stateOne && !stateNotOne))
    return;

  // Definitely not 0 or 1
  if(!stateZero && stateNotZero && !stateOne && stateNotOne) {
    std::cerr << "BAD!!!\n";
    emitBadReport(stateZero, stateOne, C);
    return;
  }

  std::cerr << "Can't determine correctness\n";
  emitUnderconstrainedReport(stateZero, stateOne, C);
  */
}

#if 0
/*
Not clear why this doesn't work, but e.g.:

int f(int x)
    {
    if (x == 1)
	return 2;
    if (x > 1)
	return x;
    return 1;
    }

check is not defined for return x, even though isZero and isOne are!
*/

void ReturnBoolChecker::checkPreStmt(const ReturnStmt *RS,
				     CheckerContext &C) const {
  std::cerr << "RS\n";
  RS->dump();
 
  const Expr *RetE = RS->getRetValue();
  if (!RetE)
    return;

  RetE->dump();

  ASTContext &AC = C.getASTContext();
  const FunctionDecl *fn = FindDecl(RS, AC);
  fn->dump();

  const AttrVec &Attrs = fn->getAttrs();
  if (!hasSpecificAttr<ReturnsBoolAttr>(Attrs))
    return;
  
  std::cerr << "BOOL!\n";

  ProgramStateRef state = C.getState();

  SValBuilder &svalBuilder = C.getSValBuilder();

  Optional<DefinedSVal> V = state->getSVal(RetE, C.getLocationContext())
      .castAs<DefinedSVal>();
  if (!V) {
    std::cerr << "Can't get V\n";
    return;
  }
    
  // FIXME: use the same type as V throughout...
  ASTContext &Ctx = svalBuilder.getContext();
  DefinedSVal Zero = svalBuilder.makeIntVal(0, Ctx.IntTy);
  DefinedSVal One = svalBuilder.makeIntVal(1, Ctx.IntTy);
  SVal isZero = svalBuilder.evalBinOp(state, BO_EQ, *V, Zero, Ctx.IntTy);
  SVal isOne = svalBuilder.evalBinOp(state, BO_EQ, *V, One, Ctx.IntTy);
  SVal check = svalBuilder.evalBinOp(state, BO_Or, isZero, isOne, Ctx.IntTy);

  std::cerr << "Zero = "; Zero.dump(); std::cerr << '\n';
  std::cerr << "isZero = "; isZero.dump(); std::cerr << '\n';
  std::cerr << "One = "; One.dump(); std::cerr << '\n';
  std::cerr << "isOne = "; isOne.dump(); std::cerr << '\n';
  std::cerr << "check = "; check.dump(); std::cerr << '\n';
  std::cerr << std::flush;
  
  ConstraintManager &CM = state->getStateManager().getConstraintManager();

  ProgramStateRef stateZero, stateNotZero;
  std::tie(stateZero, stateNotZero) = CM.assumeDual(state, isZero.castAs<DefinedSVal>());

  std::cerr << (stateZero ? "Zero" : "not Zero") << '\n';
  std::cerr << (stateNotZero ? "NotZero" : "not NotZero") << '\n';
  
  ProgramStateRef stateOne, stateNotOne;
  std::tie(stateOne, stateNotOne) = CM.assumeDual(state, isOne.castAs<DefinedSVal>());

  std::cerr << (stateOne ? "One" : "not One") << '\n';
  std::cerr << (stateNotOne ? "NotOne" : "not NotOne") << '\n';
  
  ProgramStateRef right = CM.assume(state, check.castAs<DefinedSVal>(), true);
  std::cerr << (right ? "Right" : "Not Right") << '\n';
  ProgramStateRef wrong = CM.assume(state, check.castAs<DefinedSVal>(), false);
  std::cerr << (wrong ? "Wrong" : "Not Wrong") << '\n';
}
#endif
 
void ento::registerReturnBoolChecker(CheckerManager &mgr) {
  mgr.registerChecker<ReturnBoolChecker>();
}
