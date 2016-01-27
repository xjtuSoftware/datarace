/*
 * RuntimeDataManager.h
 *
 *  Created on: Jun 10, 2014
 *      Author: ylc
 */

#ifndef RUNTIMEDATAMANAGER_H_
#define RUNTIMEDATAMANAGER_H_

#include "klee/Internal/Module/KInstruction.h"

#include "Trace.h"
#include "Prefix.h"
#include <set>
#include <map>
namespace klee {

class RuntimeDataManager {

private:
	std::vector<Trace*> traceList; // store all traces;
	Trace* currentTrace; // trace associated with current execution
	std::set<Trace*> testedTraceList; // traces which have been examined
	std::list<Prefix*> scheduleSet; // prefixes which have not been examined

public:
	//newly added stastic info
	unsigned allFormulaNum;
	unsigned allGlobal;
	unsigned brGlobal;
	unsigned solvingTimes;
	unsigned satBranch;
	unsigned unSatBranch;
	double runningCost;
	double solvingCost;
	double satCost;
	double unSatCost;
	RuntimeDataManager();
	virtual ~RuntimeDataManager();

	Trace* createNewTrace(unsigned traceId);
	Trace* getCurrentTrace();
	void addScheduleSet(Prefix* prefix);
	void printCurrentTrace(bool file);
	Prefix* getNextPrefix();
	void clearAllPrefix();
	bool isCurrentTraceUntested();
	void printAllPrefix(std::ostream &out);
	void printAllTrace(std::ostream &out);

	std::set<std::pair<unsigned, unsigned> > linepair;
	std::set<std::string> raceVarName;
	std::set<std::pair<std::string, std::string> > eventPair;
};

}
#endif /* RUNTIMEDATAMANAGER_H_ */
