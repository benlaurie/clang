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

static const FunctionDecl *FindDecl(const Stmt *s, ASTContext &AC) {
  ArrayRef<ast_type_traits::DynTypedNode> A = AC.getParents(*s);

  //llvm::raw_os_ostream cerr(std::cerr);
  for (ast_type_traits::DynTypedNode a : A) {
    //std::cerr << "-----\n";
    //a.dump(cerr, AC.getSourceManager());
    //cerr.flush();
    const FunctionDecl *fn = a.get<FunctionDecl>();
    if (fn)
      return fn;
    const Stmt *stmt = a.get<Stmt>();
    if (stmt) {
      fn = FindDecl(stmt, AC);
      if (fn)
	return fn;
    }
  }
  return nullptr;
}

void ReturnBoolChecker::checkPostCall(const CallEvent &Call,
				      CheckerContext &C) const {
  const Decl *decl = Call.getDecl();

  const AttrVec &Attrs = decl->getAttrs();
  if (!hasSpecificAttr<ReturnsBoolAttr>(Attrs))
    return;

  QualType type = Call.getResultType();

  SValBuilder &svalBuilder = C.getSValBuilder();
  DefinedSVal Two = svalBuilder.makeIntVal(2, type);
  
  ProgramStateRef state = C.getState();

  SVal V = Call.getReturnValue();

  state = state->assumeInBound(V.castAs<DefinedOrUnknownSVal>(), Two, true);

  C.addTransition(state);
}

void ReturnBoolChecker::checkPreStmt(const ReturnStmt *RS,
				     CheckerContext &C) const {
  std::cerr << "RS\n";
  RS->dump();
 
  const Expr *RetE = RS->getRetValue();
  if (!RetE)
    return;

  ASTContext &AC = C.getASTContext();
  const FunctionDecl *fn = FindDecl(RS, AC);

  const AttrVec &Attrs = fn->getAttrs();
  if (!hasSpecificAttr<ReturnsBoolAttr>(Attrs))
    return;
  
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
  
  emitUnderconstrainedReport(inRange, outRange, C);
}

 
void ento::registerReturnBoolChecker(CheckerManager &mgr) {
  mgr.registerChecker<ReturnBoolChecker>();
}
