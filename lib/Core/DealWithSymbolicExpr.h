//by hy 2015.7.21

#ifndef DEAL_WITH_SYMBOLIC_EXPR_H
#define DEAL_WITH_SYMBOLIC_EXPR_H

#include "klee/Expr.h"
#include "Event.h"
#include "Trace.h"
#include <vector>
#include <map>
#include <string>

namespace klee {

class DealWithSymbolicExpr {

private:

	void resolveSymbolicExpr(ref<Expr> value, std::set<std::string>* relatedSymbolicExpr);
	void resolveGlobalVarName(ref<Expr> value);
	std::set<std::string> allRelatedSymbolicExpr;
	void resolveSymbolicExpr(ref<klee::Expr> value);



public:
	void filterUseless(Trace* trace);
	void addExprToSet(std::set<std::string>* Expr, std::set<std::string>* relatedSymbolicExpr);
	void filterUselessWithSet(Trace* trace, std::set<std::string>* relatedSymbolicExpr);
	std::string getVarName(ref<Expr> value);
	std::string getFullName(ref<Expr> value);
	void getGlobalFirstOrderRelated(Trace* trace);
	void getGlobalVarAllRelated(Trace * trace, std::string);
	void getUsefulGlobalVar(Trace * trace, std::string);
	void getBaseUsefulExpr(Trace* trace, std::string);
	void getGlobalVarRelatedLock(Trace* trace);
	void getUsefulLockPair(Trace* trace);
	void copyCollectedDataOfTrace(Trace* trace);
	void getPathCondition(Trace* trace);

};

}

#endif
