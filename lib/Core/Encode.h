/*
 * Encode.h
 *
 *  Created on: Jun 10, 2014
 *      Author: xdzhang
 */

#ifndef ENCODE_H_
#define ENCODE_H_

#include "Event.h"
#include "RuntimeDataManager.h"
#include "DealWithSymbolicExpr.h"
#include "Trace.h"
#include <z3++.h>
#include <stack>
#include <utility>
enum InstType {
	NormalOp, GlobalVarOp, ThreadOp
};
using namespace llvm;
using namespace z3;
using namespace std;
namespace klee {

class Encode {
private:
	RuntimeDataManager& runtimeData;
	Trace* trace; //all data about encoding
	context& z3_ctx;
	solver& z3_solver;
	DealWithSymbolicExpr filter;
	double solvingCost;
	unsigned formulaNum;
	unsigned solvingTimes;

public:
	Encode(RuntimeDataManager& data, context& c, solver& s) :
			runtimeData(data), z3_ctx(c), z3_solver(s) {
		trace = data.getCurrentTrace();
		solvingCost = 0.0;
		formulaNum = 0;
		solvingTimes = 0;
	}
	~Encode() {
		runtimeData.allFormulaNum += formulaNum;
		runtimeData.solvingTimes += solvingTimes;
	}
	void buildAllFormula();
	void showInitTrace();
	void check_output();
	void check_if();
	bool verify();
	//add for harmful data race detection
	//in order to use in data race insert here.
	struct globalEvent {
		Event *preEvent;
		Event *event;
		Event *postEvent;
	};
	struct racePair {
		struct globalEvent event1;
		struct globalEvent event2;
	};
	struct Pair {
		int order; //the order of a event
		Event *event;
	};
	struct OrderPair {
		int lower;
		int upper;
	};

	void printEventSeq(vector<Event *> &eventSequence);
	void buildRaceFormula();
	void addBrConstraint(Event *);
	void buildRaceTrace();
	void buildRaceTraceFromLockSet();
	void getRaceCandidate(vector<struct globalEvent> &readGlobalSet,
			vector<struct globalEvent> &writeGlobalSet);
	void raceFromCandidate(vector<struct racePair> &raceCandidate);
	void getAltSequence(vector<struct Pair> &, struct racePair &,
			struct OrderPair &, z3::model &m);
	void getPossibleRaceTrace();
	void getEventSequence(vector<struct Pair> &, vector<Event *> &, Event *, Event *);
	void exchangeUnderEqual(vector<struct Pair> &, struct racePair &);
	void addReadWriteSet(struct globalEvent &, std::map<string, string> &, std::set<string> &);
	void deleteReadWriteSet(map<string, string> &, std::set<string> &);
	void buildPartialRaceFormula();
	void getDataFromCopy();

	std::string getVarName(ref<Expr> value);
	std::string getFullName(ref<Expr> value);
	void getGlobalFirstOrderRelated(Trace* trace);
	void getUsefulGlobalVar(Trace * trace, std::string);
	void getUsefulReadWriteSet(Trace* trace, std::string);
	void getGlobalVarRelatedLock(Trace* trace);
	void getUsefulLockPair(Trace* trace);
	void getPathCondition(Trace* trace);

	void reconstructExprs(std::string );

	void computeTrimedRaceTrace(vector<struct racePair> &raceCandidate);
	int getTotalInstOfTrace();


private:

	void resolveGlobalVarName(ref<Expr> value);
	////////////////////////////////modify this sagment at the end/////////////////////////
	vector<pair<expr, expr> > globalOutputFormula;
	//first--equality, second--constrait which equality must satisfy.

	vector<pair<Event*, expr> > ifFormula;
	vector<pair<Event*, expr> > assertFormula;
	vector<pair<Event*, expr> > rwFormula;

	void buildInitValueFormula();
	void buildPathCondition();
	void buildMemoryModelFormula();
	void buildPartialOrderFormula();
	void buildReadWriteFormula();
	void buildSynchronizeFormula();
	void buildOutputFormula();

	expr buildExprForConstantValue(Value *V, bool isLeft, string prefix);

private:
	void markLatestWriteForGlobalVar();

	map<string, Event*> latestWriteOneThread;
	map<int, map<string, Event*> > allThreadLastWrite;
	map<string, expr> eventNameInZ3; //int:eventid.add data in function buildMemoryModelFormula
	z3::sort llvmTy_to_z3Ty(const Type *typ);

	//key--local var, value--index..like ssa
	expr makeExprsAnd(vector<expr> exprs);
	expr makeExprsOr(vector<expr> exprs);
	expr makeExprsSum(vector<expr> exprs);
	expr enumerateOrder(Event *read, Event *write, Event *anotherWrite);
	expr readFromWriteFormula(Event *read, Event *write, string var);
	bool readFromInitFormula(Event * read, expr& ret);

	void computePrefix(vector<Event*>& vecEvent, Event* ifEvent);
	void showPrefixInfo(Prefix* prefix, Event* ifEvent);

	void printSourceLine(string path, vector<struct Pair *>& eventIndexPair);
	void printSourceLine(string path, vector<Event *>& trace);
	string readLine(string filename, unsigned line);
	bool isAssert(string filename, unsigned line);
	string stringTrim(char * source);
	InstType getInstOpType(Event *event);
	void logStatisticInfo();

	void controlGranularity(int level);
	void repartitionGranularity(int &uniqueNum);
	void rebuildMemoryModel();
	void getUsefulBr();
	void rebuildPathCondition();

	void makeUnrelatedConcrete(std::string, Event *);
	void makePreEventConcrete(Event *, Event *);

};

}

#endif /* ENCODE_H_ */
