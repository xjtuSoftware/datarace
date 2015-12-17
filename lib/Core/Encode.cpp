/*
 * Encode.cpp
 *
 *  Created on: Jun 10, 2014
 *      Author: xdzhang
 */
#include "Encode.h"
#include "Common.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/TypeBuilder.h"
#else
#include "llvm/Attributes.h"
#include "llvm/BasicBlock.h"
#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
#include "llvm/Target/TargetData.h"
#else
#include "llvm/DataLayout.h"
#include "llvm/TypeBuilder.h"
#endif
#endif
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <vector>
#include <sstream>
#include <assert.h>
#include <sys/time.h>
#include <fstream>
#include <pthread.h>
#include "Prefix.h"
#include <z3.h>
#include <z3_api.h>
#include <iostream>
#include <iomanip>
#include <cstdlib>
#include "KQuery2Z3.h"

#define FORMULA_DEBUG 0
#define BRANCH_INFO 1
#define BUFFERSIZE 300
#define BIT_WIDTH 64
#define POINT_BIT_WIDTH 64
#define MAKE_CONCRETE 1

#define INT_ARITHMETIC 1

using namespace llvm;
using namespace std;
using namespace z3;
namespace klee {

static std::set<std::string> relatedVarName;

void Encode::buildAllFormula() {
	buildInitValueFormula();
	buildPathCondition();
	buildMemoryModelFormula();
	buildPartialOrderFormula();
	buildReadWriteFormula();
	buildSynchronizeFormula();
	//debug: test satisfy of the model
//	check_result result = z3_solver.check();
//	if (result != z3::sat) {
//		assert(0 && "failed");
//	}
//	else assert(0 && "success");
	//
	cerr << "\nEncoding is over!\n";
}

void Encode::getDataFromCopy()
{
	trace->readSet.clear();
	trace->writeSet.clear();
	trace->all_lock_unlock.clear();
	trace->global_variable_initializer.clear();
	trace->readSet.insert(trace->copyReadSet.begin(), trace->copyReadSet.end());
	trace->writeSet.insert(trace->copyWriteSet.begin(), trace->copyWriteSet.end());
	trace->all_lock_unlock.insert(trace->copy_all_lock_unlock.begin(),
			trace->copy_all_lock_unlock.end());
	trace->global_variable_initializer.insert(trace->copy_global_variable_initializer.begin(),
			trace->copy_global_variable_initializer.end());
}

void Encode::buildPartialRaceFormula()
{
	buildInitValueFormula();
	buildPathCondition();
//	rebuildPathCondition();
//	rebuildMemoryModel();
	buildMemoryModelFormula();
	buildPartialOrderFormula();
//	buildReadWriteFormula();
	buildSynchronizeFormula();
}


void Encode::buildRaceFormula()
{
//	buildInitValueFormula();
//	buildPathCondition();
//	buildMemoryModelFormula();
//	buildPartialOrderFormula();
//	buildReadWriteFormula();
//	buildSynchronizeFormula();
//	std::cerr << "build race formula" << std::endl;
}


void Encode::printEventSeq(vector<Event *> &eventSequence)
{
	unsigned len = eventSequence.size();
	for (unsigned i = 0; i < len; i++) {
		cout << eventSequence[i]->threadId << " string:## "
				<< eventSequence[i]->toString() << "\n";
	}
}


int Encode::getTotalInstOfTrace()
{
	int ret = 0;
	unsigned eventLen = trace->eventList.size();
//	std::cerr << "print the event inst made race happened\n";
	for (unsigned tid = 0; tid < eventLen; tid++) {
		std::vector<Event*> *thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0, threadLen = thread->size(); index < threadLen; index++) {
			Event *event = thread->at(index);
			if (event == NULL)
				continue;
			ret++;
		}
	}
	return ret;
}


void Encode::getRaceCandidate(vector<struct globalEvent> &readGlobalSet,
		vector<struct globalEvent> &writeGlobalSet)
{
	std::cerr << "size = " << trace->raceCandidateEventName.size() << std::endl;
	std::set<unsigned>::iterator it = trace->raceCandidateEventName.begin(),
			ie = trace->raceCandidateEventName.end();
	for (; it != ie; it++) {
//		std::cerr << "event Name = " << *it << std::endl;
	}
	vector<struct racePair> raceCandidate;
	unsigned readLen = readGlobalSet.size();
	unsigned writeLen = writeGlobalSet.size();
	for (unsigned i = 0; i < readLen; i++) {
		Event *event1 = readGlobalSet[i].event;
		for (unsigned j = 0; j < writeLen; j++) {
			Event *event2 = writeGlobalSet[j].event;
			if ( (event1->threadId != event2->threadId)
					&& (event1->varName == event2->varName) ) {
//				std::cerr << "event1 name = " << event1->eventName << ", " <<
//						"event2 name = " << event2->eventName << std::endl;

//				if (trace->raceCandidateEventName.find(event1->eventId) !=
//						trace->raceCandidateEventName.end() ||
//						trace->raceCandidateEventName.find(event2->eventId) !=
//								trace->raceCandidateEventName.end()) {
				struct racePair pairTemp;
				pairTemp.event1 = readGlobalSet[i];
				pairTemp.event2 = writeGlobalSet[j];
				raceCandidate.push_back(pairTemp);
//				}
			}
		}
	}

	for (unsigned k = 0; k < writeLen; k++) {
		Event *event1 = writeGlobalSet[k].event;
		for (unsigned t = k + 1; t < writeLen; t++) {
			Event *event2 = writeGlobalSet[t].event;
			if ( (event1->threadId != event2->threadId)
					&& (event1->varName == event2->varName) ) {
//				std::cerr << "event1 name = " << event1->eventName << ", " <<
//						"event2 name = " << event2->eventName << std::endl;
//				if (trace->raceCandidateEventName.find(event1->eventId) !=
//						trace->raceCandidateEventName.end() ||
//						trace->raceCandidateEventName.find(event2->eventId) !=
//								trace->raceCandidateEventName.end()) {

				struct racePair pairTemp;
				pairTemp.event1 = writeGlobalSet[k];
				pairTemp.event2 = writeGlobalSet[t];
				raceCandidate.push_back(pairTemp);
//				}
			}
		}
	}
	raceFromCandidate(raceCandidate);
//	computeTrimedRaceTrace(raceCandidate);
}

void Encode::computeTrimedRaceTrace(vector<struct racePair> &raceCandidate)
{

	int totalInst = -1;
	vector<struct racePair> trulyRace;
	struct racePair pairTemp;
	unsigned raceLen = raceCandidate.size();
	std::cerr << "raceLen = " << raceLen << std::endl;

	totalInst = getTotalInstOfTrace();
	std::cerr << "totalInst = " << totalInst << std::endl;
	int interval = totalInst / 10;

	for (unsigned i = 0; i < raceLen; i++) {
		//define every event's expr

		expr preEvent1Expr = z3_ctx.bool_val(true);
		expr event1Expr = z3_ctx.bool_val(true);
		expr postEvent1Expr = z3_ctx.bool_val(true);

		expr preEvent2Expr = z3_ctx.bool_val(true);
		expr event2Expr = z3_ctx.bool_val(true);
		expr postEvent2Expr = z3_ctx.bool_val(true);

		expr temp1 = z3_ctx.bool_val(true);
		expr temp2 = z3_ctx.bool_val(true);
		expr preEvent1Temp = z3_ctx.bool_val(true);
		expr postEvent1Temp = z3_ctx.bool_val(true);
		expr preEvent2Temp = z3_ctx.bool_val(true);
		expr postEvent2Temp = z3_ctx.bool_val(true);

		Event *preEvent1 = raceCandidate[i].event1.preEvent;
		Event *event1 = raceCandidate[i].event1.event;
		Event *postEvent1 = raceCandidate[i].event1.postEvent;

		Event *preEvent2 = raceCandidate[i].event2.preEvent;
		Event *event2 = raceCandidate[i].event2.event;
		Event *postEvent2 = raceCandidate[i].event2.postEvent;

//		std::cerr << "event1->eventId = " << event1->eventId << ", event2->eventId = " <<
//				event2->eventId << std::endl;
//		std::cerr << "value = " << (int)event1->eventId - (int)event2->eventId << std::endl;
//		if (abs((int)event1->eventId - (int)event2->eventId) > interval)
//			continue;

		event1Expr = z3_ctx.int_const(event1->eventName.c_str());
		event2Expr = z3_ctx.int_const(event2->eventName.c_str());

		//overwrite the readSet and writeSet
		std::map<string, string> record1;
		std::map<string, string> record2;
		std::set<string> initializer_record1;
		std::set<string> initializer_record2;
//		std::cerr << "before global_variable size = " <<
//				trace->global_variable_initializer.size() << std::endl;
		addReadWriteSet(raceCandidate[i].event1, record1, initializer_record1);
		addReadWriteSet(raceCandidate[i].event2, record2, initializer_record2);

//		std::cerr << "initializer_record2 size = " << initializer_record2.size() << std::endl;

//		reconstructExprs(event1->varName);
//		z3_solver.push();
//		buildPartialRaceFormula();

//		std::cerr << "test for pre and post\n";
//		std::cerr << "event1 eventName = " << event1->eventName << ", pre = " <<
//				event1->preEventName << ", post = " << event1->postEventName << std::endl;
//		std::cerr << "event2 eventName = " << event2->eventName << ", pre = " <<
//				event2->preEventName << ", post = " << event2->postEventName << std::endl;
		/*
		if (event1->preEventName != "Init") {
			preEvent1Expr = z3_ctx.int_const(event1->preEventName.c_str());
			preEvent1Temp = (preEvent1Expr < event2Expr);
		} else {
			preEvent1Temp = z3_ctx.bool_val(true);
		}
		if (event1->postEventName != "Over") {
			postEvent1Expr = z3_ctx.int_const(event1->postEventName.c_str());
			postEvent1Temp = (event2Expr < postEvent1Expr);
		} else {
			postEvent1Temp = z3_ctx.bool_val(true);
		}
		if (event2->preEventName != "Init") {
					preEvent2Expr = z3_ctx.int_const(event2->preEventName.c_str());
					preEvent2Temp = (preEvent2Expr < event1Expr);
		} else {
					preEvent2Temp = z3_ctx.bool_val(true);
		}
		if (event2->postEventName != "Over") {
					postEvent2Expr = z3_ctx.int_const(event2->postEventName.c_str());
					postEvent2Temp = (event1Expr < postEvent2Expr);
		} else {
					postEvent2Temp = z3_ctx.bool_val(true);
		}
		*/
		if (preEvent1 != NULL) {
					preEvent1Expr = z3_ctx.int_const(preEvent1->eventName.c_str());
					preEvent1Temp = (preEvent1Expr < event2Expr);
		} else {
					preEvent1Temp = z3_ctx.bool_val(true);
		}
		if (postEvent1 != NULL) {
					postEvent1Expr = z3_ctx.int_const(postEvent1->eventName.c_str());
					postEvent1Temp = (event2Expr < postEvent1Expr);
		} else {
					postEvent1Temp = z3_ctx.bool_val(true);
		}
		if (preEvent2 != NULL) {
					preEvent2Expr = z3_ctx.int_const(preEvent2->eventName.c_str());
					preEvent2Temp = (preEvent2Expr < event1Expr);
		} else {
					preEvent2Temp = z3_ctx.bool_val(true);
		}
		if (postEvent2 != NULL) {
					postEvent2Expr = z3_ctx.int_const(postEvent2->eventName.c_str());
					postEvent2Temp = (event1Expr < postEvent2Expr);
		} else {
					postEvent2Temp = z3_ctx.bool_val(true);
		}

		temp1 = (preEvent1Temp && postEvent1Temp);
		temp2 = (preEvent2Temp && postEvent2Temp);




//		std::cerr << "size of usefulGlobalVar = " << trace->usefulGlobalVar.size() <<
//				", event1 varName = " << event1->varName << ", event2 varName = " << event2->varName << std::endl;
//		for (std::set<std::string>::iterator it = trace->usefulGlobalVar.begin(), ie =
//				trace->usefulGlobalVar.end(); it != ie; it++) {
//			std::cerr << "use Name = " << *it << std::endl;
//		}
//		getGlobalVarRelatedLock(trace);
//		getUsefulLockPair(trace);
//		getPathCondition(trace);
		z3_solver.push();
		z3_solver.add( (temp1 && temp2) );
		buildReadWriteFormula();
		makePreEventConcrete(raceCandidate[i].event1.event, raceCandidate[i].event2.event);
//		makeUnrelatedConcrete(event1->varName, event1);
		//add br constraint before the two race insts.
//		addBrConstraint(raceCandidate[i].event1.event);
//		std::cerr << "add constraint br1\n";

//		std::cerr << "add constraint br2\n";
		z3_solver.push();
//		std::cerr << "push two\n";
		addBrConstraint(raceCandidate[i].event2.event);
		z3_solver.add( (event1Expr <= event2Expr) );
//		std::cerr << "add constraint of event\n";

//		std::cerr << z3_solver << std::endl;
		check_result result = z3_solver.check();
		std::cerr << "interleaving events: event1 Name =  " << event1->eventName <<
				" event1 Name = " << event2->eventName << "\n";
//		std::cerr << z3_solver << std::endl;
		std::cerr << "checking ...\n";
		if (result == z3::sat) {
			vector<struct Pair> altSequence;
			model m = z3_solver.get_model();
			pairTemp = raceCandidate[i];
			trulyRace.push_back(pairTemp);
			stringstream equalss, own;
			equalss << m.eval(event1Expr);
			own << m.eval(event2Expr);
			struct OrderPair op;
			op.lower =  atoi(equalss.str().c_str());
			op.upper = atoi(own.str().c_str());
			int test = atoi(own.str().c_str());
			int equalOrder = atoi(equalss.str().c_str());
			for (unsigned k = 0; k < trace->eventList.size(); k++) {
				std::vector<Event *> *thread = trace->eventList[k];
				if (thread == NULL) {
					continue;
				}
				for (unsigned j = 0; j < thread->size(); j++) {
					if (thread->at(j)->eventType == Event::VIRTUAL)
						continue;
					Event * event = thread->at(j);
					expr eventExpr = z3_ctx.int_const(event->eventName.c_str());
					stringstream ss;
					ss << m.eval(eventExpr);

					int order = atoi(ss.str().c_str());
					struct Pair temp;
					temp.order = order;
					temp.event = event;

					altSequence.push_back(temp);
				}
			}


			z3_solver.pop();
			if (equalOrder == test) {
				exchangeUnderEqual(altSequence, raceCandidate[i]);
			} else {
				getAltSequence(altSequence, raceCandidate[i], op, m);
			}
#if FORMULA_DEBUG
			stringstream output;
			output << "./output_info/" << raceCandidate[i].event1.event->eventName <<
					raceCandidate[i].event2.event->eventName << ".z3expr";
			std::ofstream out_file(output.str().c_str(),std::ios_base::out|std::ios_base::app);
			out_file <<"\n"<<z3_solver<<"\n";
			out_file <<"\nz3_solver.get_model()\n";
			out_file <<"\n"<<m<<"\n";
			out_file.close();
#endif

		} else if (result == z3::unsat) {
			z3_solver.pop();
			cerr << "there is no data race!\n";
		} else {
			z3_solver.pop();
			cerr << "The result is unknown!\n";
		}
		z3_solver.pop();
		deleteReadWriteSet(record1, initializer_record1);
		deleteReadWriteSet(record2, initializer_record2);
	}

}

void Encode::getEventSequence(vector<struct Pair> &altSequence, vector<Event *> &eventSequence,
		Event * event1, Event * event2)
{
	//bubble sort to get the altSequence.
	//after bubble sort, then can get one of the execution trace.
	vector<struct Pair>::size_type altLen = altSequence.size();
	for (vector<struct Pair>::size_type index1 = 0; index1 < altLen - 1;
				index1++) {
		for (vector<struct Pair>::size_type index2 = 0;
				index2 < altLen - index1 - 1; index2++) {
			if (altSequence[index2].order > altSequence[index2 + 1].order) {
					struct Pair temp = altSequence[index2];
					altSequence[index2] = altSequence[index2 + 1];
					altSequence[index2 + 1] = temp;
			}
		}
	}
	for (vector<struct Pair>::size_type index = 0; index < altLen;
					index++) {
		eventSequence.push_back(altSequence[index].event);
		stringstream output;
		output << "./output_info/" << event1->eventName << event2->eventName << ".z3expr";
		std::ofstream out_file(output.str().c_str(),std::ios_base::out|std::ios_base::app);
		out_file << "eventName = " << altSequence[index].event->eventName <<
				", order = " << altSequence[index].order << "\n";
		out_file.close();
	}
}

void Encode::makePreEventConcrete(Event *event1, Event *event2)
{
	int interval = 200;
	int eventId = -1;
	unsigned int totalRwExpr = rwFormula.size();
	for (unsigned int j = 0; j < totalRwExpr; j++) {
			Event* curr = rwFormula[j].first;
			if (event1->threadId == curr->threadId) {
				eventId = event1->eventId;
			} else if (event2->threadId == curr->threadId) {
				eventId = event2->eventId;
			}

			if (eventId == -1) {
				z3_solver.add(rwFormula[j].second);
			} else {
				if ((eventId - (int)curr->eventId) > interval) {
					z3_solver.add(rwFormula[j].second);
				}
			}
	}

	eventId = -1;
	std::map<std::string, std::vector<Event *> >::iterator itr =
			trace->readSet.begin(), ier = trace->readSet.end();
	unsigned total = trace->readSet.size();
	for (; itr != ier; itr++) {
		std::vector<Event *>::iterator ite = itr->second.begin(), iee = itr->second.end();
		for (; ite != iee; ite++) {
			if (event1->threadId == (*ite)->threadId) {
				eventId = event1->eventId;
			} else if (event2->threadId == (*ite)->threadId) {
				eventId = event2->eventId;
			}
			if (eventId == -1) {
				itr->second.erase(ite);
			} else {
				if (((int)(*ite)->eventId) - eventId > interval) {
					itr->second.erase(ite);
				}
			}
		}
	}
}


void Encode::makeUnrelatedConcrete(std::string str, Event *event)
{

//	std::cerr << "str = " << str << std::endl;
	trace->globalVarAllRelated.clear();
	filter.getGlobalVarAllRelated(trace, str);

	//添加读写的解
	std::set<std::string> &globalVarAllRelated = trace->globalVarAllRelated;
	std::vector<ref<klee::Expr> > &rwSymbolicExpr = trace->rwSymbolicExpr;
	std::string varName;

//	std::set<std::string>::iterator it = RelatedSymbolicExpr.begin(),
//			ie = RelatedSymbolicExpr.end();
//	for (; it != ie; it++) {
//		std::cerr << "related Var Name = " << *it << std::endl;
//	}
//	std::cerr << "size_1 = " << RelatedSymbolicExpr.size() << ", size_2 = " <<
//			rwSymbolicExpr.size() << std::endl;
#if MAKE_CONCRETE
	expr eventExpr = z3_ctx.int_const(event->eventName.c_str());
	unsigned int totalRwExpr = rwFormula.size();
	for (unsigned int j = 0; j < totalRwExpr; j++){
		varName = filter.getVarName(rwSymbolicExpr[j]->getKid(1));
		if (globalVarAllRelated.find(varName) == globalVarAllRelated.end()){
			Event* curr = rwFormula[j].first;
			expr currExpr = z3_ctx.int_const(curr->eventName.c_str());

			expr constraint = z3_ctx.bool_val(1);
			constraint = rwFormula[j].second;
//			if (curr->threadId == event->threadId) {
//				if (curr->eventId < event->eventId) {
//					constraint = rwFormula[j].second;
//				}
////				std::cerr << "curr name = " << curr->varName << std::endl;
//			} else {
//				constraint = implies(currExpr < eventExpr, rwFormula[j].second);
////				std::cerr << "curr name = " << curr->varName << std::endl;
//			}
			z3_solver.add(constraint);
//					z3_solver.add(rwFormula[j].second);
		}
	}
#endif
}


void Encode::getAltSequence(vector<struct Pair> &altSequence,
		struct racePair &localize, struct OrderPair &op, z3::model &m)
{
	vector<struct Pair> nextSequence;
	bool raceHappen = false;

	//Then get the other execution trace.
	//Add the additional constraints, the event order, and global variables constraints.
	vector<struct Pair>::size_type altLen = altSequence.size();
//	try {
//		model m = z3_solver.get_model();

	z3_solver.push();


	for (vector<struct Pair>::size_type index1 = 0; index1 < altLen; index1++) {
		if (altSequence[index1].order < op.lower) {
			if (altSequence[index1].event->isGlobal &&
					(altSequence[index1].event->inst->inst->getOpcode() == Instruction::Load ||
					altSequence[index1].event->inst->inst->getOpcode() == Instruction::Store)) {
				expr varExpr = z3_ctx.bool_val(true);
				expr valueExpr = z3_ctx.bool_val(true);
				stringstream ss;
				Type::TypeID id;
				if (altSequence[index1].event->inst->inst->getOpcode() == Instruction::Store) {
					id = altSequence[index1].event->inst->inst->getOperand(0)->getType()->getTypeID();
				} else { // instruction load.
					id = altSequence[index1].event->inst->inst->getType()->getTypeID();
				}
				if (trace->usefulGlobalVar.find(altSequence[index1].event->eventName) !=
						trace->usefulGlobalVar.end()) {
					if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
						varExpr = z3_ctx.real_const(altSequence[index1].event->globalVarFullName.c_str());
						ss << m.eval(varExpr);
						valueExpr = z3_ctx.real_val(ss.str().c_str());
					} else {
#if INT_ARITHMETIC
						varExpr = z3_ctx.int_const(altSequence[index1].event->globalVarFullName.c_str());
						ss << m.eval(varExpr);
						valueExpr = z3_ctx.int_val(ss.str().c_str());
#else
						varExpr = z3_ctx.bv_const(altSequence[index1].event->globalVarFullName.c_str(), BIT_WIDTH);
						expr temp = to_expr(z3_ctx, Z3_mk_bv2int(z3_ctx, m.eval(varExpr), true));
						std::cerr << "m.eval = " << m.eval(varExpr) << std::endl;
						ss << m.eval(temp);
						valueExpr = z3_ctx.bv_val(atoi(ss.str().c_str()), BIT_WIDTH);
#endif
					}
					z3_solver.add((varExpr == valueExpr));
				}
			}
		}
	}
//	} catch(z3::exception &e) {
//		std::cerr << "exception : " << e << std::endl;
//	}

	for (vector<struct Pair>::size_type index1 = 0; index1 < altLen; index1++) {
		if (altSequence[index1].order > op.upper) {
//			std::cerr << "event Name = " << altSequence[index1].event->eventName <<
//							", event Order = " << altSequence[index1].order << std::endl;
			expr eventExpr = z3_ctx.int_const(altSequence[index1].event->eventName.c_str());
			expr orderExpr = z3_ctx.int_val(altSequence[index1].order);
			z3_solver.add((eventExpr == orderExpr));
		}
		if (altSequence[index1].order < op.lower) {
//			std::cerr << "event Name = " << altSequence[index1].event->eventName <<
//							", event Order = " << altSequence[index1].order << std::endl;
			expr eventExpr = z3_ctx.int_const(altSequence[index1].event->eventName.c_str());
			expr orderExpr = z3_ctx.int_val(altSequence[index1].order);
			z3_solver.add((eventExpr == orderExpr));
		}

	}
	addBrConstraint(localize.event1.event);
	expr event1Expr = z3_ctx.int_const(localize.event1.event->eventName.c_str());
	expr event2Expr = z3_ctx.int_const(localize.event2.event->eventName.c_str());
	z3_solver.add((event1Expr > event2Expr));

	check_result result = z3_solver.check();
	std::cerr << "OK and checking alt sequence\n";
	if (result == z3::sat) {
		model m = z3_solver.get_model();
		stringstream equalss, own;
		equalss << m.eval(event1Expr);
		own << m.eval(event2Expr);
		int test = atoi(own.str().c_str());
		int equalOrder = atoi(equalss.str().c_str());
		for (unsigned k = 0; k < trace->eventList.size(); k++) {
				std::vector<Event *> *thread = trace->eventList[k];
				if (thread == NULL) {
						continue;
				}
				for (unsigned j = 0; j < thread->size(); j++) {
					if (thread->at(j)->eventType == Event::VIRTUAL)
						continue;
					Event * event = thread->at(j);
					expr eventExpr = z3_ctx.int_const(event->eventName.c_str());
					stringstream ss;
					ss << m.eval(eventExpr);

					int order = atoi(ss.str().c_str());
					struct Pair temp;
					temp.order = order;
					temp.event = event;

					nextSequence.push_back(temp);
				}
		}
		raceHappen = true;
		std::cerr << "one pair race detected!\n";
		std::cerr << "dataRace " << localize.event1.event->eventName <<
				" " << localize.event2.event->eventName << "\n";
	}else if (result == z3::unsat) {
		cerr << "there is no data race!\n";
	} else {
		cerr << "The result is unknown!\n";
	}
	z3_solver.pop();
	if (raceHappen) {
		std::cerr << "get the race happend" << std::endl;
		vector<Event *> vecEvent1;
		vector<Event *> vecEvent2;
		//get two trace. bubble sort the sequence: altSequence and nextSequence
		stringstream ss1, ss2;
		ss1 << localize.event1.event->eventName << localize.event2.event->eventName;
		getEventSequence(altSequence, vecEvent1, localize.event1.event, localize.event2.event);
//		printEventSeq(vecEvent1);

		Prefix* prefix = new Prefix(vecEvent1, trace->createThreadPoint,
									ss1.str());
		prefix->setRacePos((int)localize.event2.event->eventId);
//		std::cerr << "ss1.str = " << ss1.str() << std::endl;
		showPrefixInfo(prefix, 0);
		runtimeData.addScheduleSet(prefix);

		ss2 << localize.event2.event->eventName << localize.event1.event->eventName;
		getEventSequence(nextSequence, vecEvent2, localize.event2.event, localize.event1.event);
//		printEventSeq(vecEvent2);
		Prefix *prefix1 = new Prefix(vecEvent2, trace->createThreadPoint, ss2.str());
		prefix1->setRacePos((int)localize.event1.event->eventId);
//		std::cerr << "ss2.str = " << ss2.str() << std::endl;
		showPrefixInfo(prefix1, 0);
		runtimeData.addScheduleSet(prefix1);
#if FORMULA_DEBUG
		stringstream output1;
		output1 << "./output_info/" << prefix1->getName() << ".z3expr";
		std::ofstream out_file1(output1.str().c_str(),std::ios_base::out|std::ios_base::app);
		out_file1 <<"\n"<<z3_solver<<"\n";
		model m1 = z3_solver.get_model();
		out_file1 <<"\nz3_solver.get_model()\n";
		out_file1 <<"\n"<<m1<<"\n";
		out_file1.close();
#endif
	}

}


void Encode::exchangeUnderEqual(vector<struct Pair> &altSequence, struct racePair &localize)
{
	int sOrder = -1;
	int eOrder = -1;
	//get the altSequence to execute compare the result.
	vector<Event *> vecEvent;
	getEventSequence(altSequence, vecEvent, localize.event1.event, localize.event2.event);
	vector<struct Pair>::size_type len = altSequence.size();
	for (vector<struct Pair>::size_type index = 0; index < len; index++) {
		if (altSequence[index].event->eventName == localize.event1.event->eventName
				|| altSequence[index].event->eventName == localize.event2.event->eventName) {
			if (altSequence[index].event->inst->inst->getOpcode() == Instruction::Load ||
					altSequence[index].event->inst->inst->getOpcode() == Instruction::Store) {
				if (sOrder == -1) {
					sOrder = index;
					continue;
				}
				if (eOrder == -1)
					eOrder = index;
				}
			}
	}

	vector<Event *> beforeSecondEvent;
	vector<Event *> otherEvent;

	Event * firstTemp = vecEvent[sOrder];
	Event * secondTemp = vecEvent[eOrder];

	for (int t = sOrder + 1; t < eOrder; t++) {
		if (vecEvent[t]->eventName == vecEvent[eOrder]->eventName) {
			beforeSecondEvent.push_back(vecEvent[t]);
		} else {
			otherEvent.push_back(vecEvent[t]);
		}
	}
	for (unsigned k = 0, start = sOrder; k < beforeSecondEvent.size(); k++) {
		vecEvent[start++] = beforeSecondEvent[k];
	}
	int firstPos = sOrder + beforeSecondEvent.size();
	int secondPos = firstPos + 1;
	vecEvent[firstPos] = firstTemp;
	vecEvent[secondPos] = secondTemp;
	for (unsigned k = 0, start = firstPos + 2; k < otherEvent.size(); k++) {
		vecEvent[start++] = otherEvent[k];
	}

	std::cerr << "one pair race detected!\n";
	std::cerr << "firstPos = " << firstPos << ", secondPos = " << secondPos << std::endl;
	stringstream ss;
	ss << vecEvent[firstPos]->eventName << vecEvent[secondPos]->eventName;
	std::cerr << "ss1.name = " << ss.str() << std::endl;
//	printEventSeq(vecEvent);
	Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint,
								ss.str());
	prefix->setRacePos((int)vecEvent[secondPos]->eventId);
	showPrefixInfo(prefix, 0);
#if FORMULA_DEBUG
	stringstream output;
	output << "./output_info/" << prefix->getName() << ".z3expr";
	std::ofstream out_file(output.str().c_str(),std::ios_base::out|std::ios_base::app);
	out_file <<"\n"<<z3_solver<<"\n";
	model m = z3_solver.get_model();
	out_file <<"\nz3_solver.get_model()\n";
	out_file <<"\n"<<m<<"\n";
	out_file.close();
#endif
	runtimeData.addScheduleSet(prefix);
	ss.str("");

	Event *changeEvent = vecEvent[firstPos];
	vecEvent[firstPos] = vecEvent[secondPos];
	vecEvent[secondPos] = changeEvent;
	ss << vecEvent[firstPos]->eventName << vecEvent[secondPos]->eventName;
	std::cerr << "ss2.name = " << ss.str() << std::endl;
//	printEventSeq(vecEvent);
	Prefix *prefix1 = new Prefix(vecEvent, trace->createThreadPoint, ss.str());
	prefix1->setRacePos((int)vecEvent[secondPos]->eventId);
	showPrefixInfo(prefix1, 0);
#if FORMULA_DEBUG
	stringstream output1;
	output1 << "./output_info/" << prefix1->getName() << ".z3expr";
	std::ofstream out_file1(output1.str().c_str(),std::ios_base::out|std::ios_base::app);
	out_file1 <<"\n"<<z3_solver<<"\n";
	model m1 = z3_solver.get_model();
	out_file1 <<"\nz3_solver.get_model()\n";
	out_file1 <<"\n"<<m1<<"\n";
	out_file1.close();
#endif
	runtimeData.addScheduleSet(prefix1);
	ss.str("");
}

void Encode::addReadWriteSet(struct globalEvent & opPair,
		std::map<string, string> &record, std::set<string> &initializer_record)
{
	if (opPair.preEvent != NULL && opPair.preEvent->isGlobal) {
		string tmpStr = opPair.preEvent->varName;
		if (opPair.preEvent->inst->inst->getOpcode() == Instruction::Load) {
			if (trace->readSet.count(tmpStr) == 0 &&
					trace->copyReadSet.count(tmpStr) == 1) {
				trace->readSet.insert(make_pair(tmpStr,
						trace->copyReadSet[tmpStr]));
				record.insert(make_pair("read", tmpStr));
			}
		} else if (opPair.preEvent->inst->inst->getOpcode() == Instruction::Store) {
			if (trace->writeSet.count(opPair.preEvent->varName) == 0 &&
					trace->copyWriteSet.count(tmpStr) == 1) {
				trace->writeSet.insert(make_pair(opPair.preEvent->varName,
						trace->copyWriteSet[opPair.preEvent->varName]));
				record.insert(make_pair("write", opPair.preEvent->varName));
			}
		}
//		if (trace->global_variable_initializer.count(tmpStr) == 0 &&
//				trace->copy_global_variable_initializer.count(tmpStr) == 1) {
//			trace->global_variable_initializer.insert(make_pair(tmpStr,
//					trace->copy_global_variable_initializer[tmpStr]));
//			initializer_record.insert(tmpStr);
//		}
	}
	if (opPair.event->isGlobal) {
		string tmpStr = opPair.event->varName;
		if (opPair.event->inst->inst->getOpcode() == Instruction::Load) {
			if (trace->readSet.count(tmpStr) == 0 &&
					trace->copyReadSet.count(tmpStr) == 1) {
				trace->readSet.insert(make_pair(tmpStr,
						trace->copyReadSet[tmpStr]));
				record.insert(make_pair("read", tmpStr));
			}
		} else if (opPair.event->inst->inst->getOpcode() == Instruction::Store) {
			if (trace->writeSet.count(opPair.event->varName) == 0 &&
					trace->copyWriteSet.count(tmpStr) == 1) {
				trace->writeSet.insert(make_pair(opPair.event->varName,
						trace->copyWriteSet[opPair.event->varName]));
				record.insert(make_pair("write", opPair.event->varName));
			}
		}
//		if (trace->global_variable_initializer.count(tmpStr) == 0 &&
//				trace->copy_global_variable_initializer.count(tmpStr) == 1) {
//			trace->global_variable_initializer.insert(make_pair(tmpStr,
//					trace->copy_global_variable_initializer[tmpStr]));
//			initializer_record.insert(tmpStr);
//		}
	}
	if (opPair.postEvent != NULL && opPair.postEvent->isGlobal) {
		string tmpStr = opPair.postEvent->varName;
		if (opPair.postEvent->inst->inst->getOpcode() == Instruction::Load) {
			if (trace->readSet.count(tmpStr) == 0 &&
					trace->copyReadSet.count(tmpStr) == 1) {
				trace->readSet.insert(make_pair(tmpStr,
						trace->copyReadSet[tmpStr]));
				record.insert(make_pair("read", tmpStr));
			}
		} else if (opPair.postEvent->inst->inst->getOpcode() == Instruction::Store) {
			if (trace->writeSet.count(tmpStr) == 0 &&
					trace->copyWriteSet.count(tmpStr) == 1) {
				trace->writeSet.insert(make_pair(tmpStr,
						trace->copyWriteSet[tmpStr]));
				record.insert(make_pair("write", tmpStr));
			}
		}
//		if (trace->global_variable_initializer.count(tmpStr) == 0 &&
//				trace->copy_global_variable_initializer.count(tmpStr) == 1) {
//			trace->global_variable_initializer.insert(make_pair(tmpStr,
//					trace->copy_global_variable_initializer[tmpStr]));
//			initializer_record.insert(tmpStr);
//		}
	}

}


void Encode::deleteReadWriteSet(map<string, string> &record, set<string> &initializer_record)
{
	for (std::map<string, string>::iterator it = record.begin(); it != record.end(); it++) {
		if (it->first == "read") {
			trace->readSet.erase(it->second);
		}
		if (it->first == "write") {
			trace->writeSet.erase(it->second);
		}
	}

	for (std::set<string>::iterator it = initializer_record.begin();
			it != initializer_record.end(); it++) {
		std::cerr << "deleteReadWriteSet" << std::endl;
		trace->global_variable_initializer.erase(*it);
	}
}

void Encode::reconstructExprs(std::string str)
{
	getDataFromCopy();
	getUsefulReadWriteSet(trace, str);
//	getGlobalVarRelatedLock(trace);
	getUsefulLockPair(trace);
	getPathCondition(trace);
}

void Encode::raceFromCandidate(vector<struct racePair> &raceCandidate)
{
	vector<struct racePair> trulyRace;
	struct racePair pairTemp;
	unsigned raceLen = raceCandidate.size();
	std::cerr << "raceLen = " << raceLen << std::endl;

	for (unsigned i = 0; i < raceLen; i++) {
		//define every event's expr

		expr preEvent1Expr = z3_ctx.bool_val(true);
		expr event1Expr = z3_ctx.bool_val(true);
		expr postEvent1Expr = z3_ctx.bool_val(true);

		expr preEvent2Expr = z3_ctx.bool_val(true);
		expr event2Expr = z3_ctx.bool_val(true);
		expr postEvent2Expr = z3_ctx.bool_val(true);

		expr temp1 = z3_ctx.bool_val(true);
		expr temp2 = z3_ctx.bool_val(true);
		expr preEvent1Temp = z3_ctx.bool_val(true);
		expr postEvent1Temp = z3_ctx.bool_val(true);
		expr preEvent2Temp = z3_ctx.bool_val(true);
		expr postEvent2Temp = z3_ctx.bool_val(true);

		Event *preEvent1 = raceCandidate[i].event1.preEvent;
		Event *event1 = raceCandidate[i].event1.event;
		Event *postEvent1 = raceCandidate[i].event1.postEvent;

		Event *preEvent2 = raceCandidate[i].event2.preEvent;
		Event *event2 = raceCandidate[i].event2.event;
		Event *postEvent2 = raceCandidate[i].event2.postEvent;

		event1Expr = z3_ctx.int_const(event1->eventName.c_str());
		event2Expr = z3_ctx.int_const(event2->eventName.c_str());

		//overwrite the readSet and writeSet
		std::map<string, string> record1;
		std::map<string, string> record2;
		std::set<string> initializer_record1;
		std::set<string> initializer_record2;
//		std::cerr << "before global_variable size = " <<
//				trace->global_variable_initializer.size() << std::endl;
		addReadWriteSet(raceCandidate[i].event1, record1, initializer_record1);
		addReadWriteSet(raceCandidate[i].event2, record2, initializer_record2);

//		std::cerr << "initializer_record2 size = " << initializer_record2.size() << std::endl;

//		reconstructExprs(event1->varName);
//		z3_solver.push();
//		buildPartialRaceFormula();

//		std::cerr << "test for pre and post\n";
//		std::cerr << "event1 eventName = " << event1->eventName << ", pre = " <<
//				event1->preEventName << ", post = " << event1->postEventName << std::endl;
//		std::cerr << "event2 eventName = " << event2->eventName << ", pre = " <<
//				event2->preEventName << ", post = " << event2->postEventName << std::endl;
		/*
		if (event1->preEventName != "Init") {
			preEvent1Expr = z3_ctx.int_const(event1->preEventName.c_str());
			preEvent1Temp = (preEvent1Expr < event2Expr);
		} else {
			preEvent1Temp = z3_ctx.bool_val(true);
		}
		if (event1->postEventName != "Over") {
			postEvent1Expr = z3_ctx.int_const(event1->postEventName.c_str());
			postEvent1Temp = (event2Expr < postEvent1Expr);
		} else {
			postEvent1Temp = z3_ctx.bool_val(true);
		}
		if (event2->preEventName != "Init") {
					preEvent2Expr = z3_ctx.int_const(event2->preEventName.c_str());
					preEvent2Temp = (preEvent2Expr < event1Expr);
		} else {
					preEvent2Temp = z3_ctx.bool_val(true);
		}
		if (event2->postEventName != "Over") {
					postEvent2Expr = z3_ctx.int_const(event2->postEventName.c_str());
					postEvent2Temp = (event1Expr < postEvent2Expr);
		} else {
					postEvent2Temp = z3_ctx.bool_val(true);
		}
		*/
		if (preEvent1 != NULL) {
					preEvent1Expr = z3_ctx.int_const(preEvent1->eventName.c_str());
					preEvent1Temp = (preEvent1Expr < event2Expr);
		} else {
					preEvent1Temp = z3_ctx.bool_val(true);
		}
		if (postEvent1 != NULL) {
					postEvent1Expr = z3_ctx.int_const(postEvent1->eventName.c_str());
					postEvent1Temp = (event2Expr < postEvent1Expr);
		} else {
					postEvent1Temp = z3_ctx.bool_val(true);
		}
		if (preEvent2 != NULL) {
					preEvent2Expr = z3_ctx.int_const(preEvent2->eventName.c_str());
					preEvent2Temp = (preEvent2Expr < event1Expr);
		} else {
					preEvent2Temp = z3_ctx.bool_val(true);
		}
		if (postEvent2 != NULL) {
					postEvent2Expr = z3_ctx.int_const(postEvent2->eventName.c_str());
					postEvent2Temp = (event1Expr < postEvent2Expr);
		} else {
					postEvent2Temp = z3_ctx.bool_val(true);
		}

		temp1 = (preEvent1Temp && postEvent1Temp);
		temp2 = (preEvent2Temp && postEvent2Temp);




//		std::cerr << "size of usefulGlobalVar = " << trace->usefulGlobalVar.size() <<
//				", event1 varName = " << event1->varName << ", event2 varName = " << event2->varName << std::endl;
//		for (std::set<std::string>::iterator it = trace->usefulGlobalVar.begin(), ie =
//				trace->usefulGlobalVar.end(); it != ie; it++) {
//			std::cerr << "use Name = " << *it << std::endl;
//		}
//		getGlobalVarRelatedLock(trace);
//		getUsefulLockPair(trace);
//		getPathCondition(trace);
		z3_solver.push();
		z3_solver.add( (temp1 && temp2) );
		buildReadWriteFormula();
//		makePreEventConcrete(raceCandidate[i].event1.event, raceCandidate[i].event2.event);
//		makeUnrelatedConcrete(event1->varName, event1);
		//add br constraint before the two race insts.
//		addBrConstraint(raceCandidate[i].event1.event);
//		std::cerr << "add constraint br1\n";

//		std::cerr << "add constraint br2\n";
		z3_solver.push();
//		std::cerr << "push two\n";
		addBrConstraint(raceCandidate[i].event2.event);
		z3_solver.add( (event1Expr <= event2Expr) );
//		std::cerr << "add constraint of event\n";

//		std::cerr << z3_solver << std::endl;
		check_result result = z3_solver.check();
		std::cerr << "interleaving events: event1 Name =  " << event1->eventName <<
				" event1 Name = " << event2->eventName << "\n";
//		std::cerr << z3_solver << std::endl;
		std::cerr << "checking ...\n";
		if (result == z3::sat) {
			vector<struct Pair> altSequence;
			model m = z3_solver.get_model();
			pairTemp = raceCandidate[i];
			trulyRace.push_back(pairTemp);
			stringstream equalss, own;
			equalss << m.eval(event1Expr);
			own << m.eval(event2Expr);
			struct OrderPair op;
			op.lower =  atoi(equalss.str().c_str());
			op.upper = atoi(own.str().c_str());
			int test = atoi(own.str().c_str());
			int equalOrder = atoi(equalss.str().c_str());
			for (unsigned k = 0; k < trace->eventList.size(); k++) {
				std::vector<Event *> *thread = trace->eventList[k];
				if (thread == NULL) {
					continue;
				}
				for (unsigned j = 0; j < thread->size(); j++) {
					if (thread->at(j)->eventType == Event::VIRTUAL)
						continue;
					Event * event = thread->at(j);
					expr eventExpr = z3_ctx.int_const(event->eventName.c_str());
					stringstream ss;
					ss << m.eval(eventExpr);

					int order = atoi(ss.str().c_str());
					struct Pair temp;
					temp.order = order;
					temp.event = event;

					altSequence.push_back(temp);
				}
			}


			z3_solver.pop();
			if (equalOrder == test) {
				exchangeUnderEqual(altSequence, raceCandidate[i]);
			} else {
				getAltSequence(altSequence, raceCandidate[i], op, m);
			}
#if FORMULA_DEBUG
			stringstream output;
			output << "./output_info/" << raceCandidate[i].event1.event->eventName <<
					raceCandidate[i].event2.event->eventName << ".z3expr";
			std::ofstream out_file(output.str().c_str(),std::ios_base::out|std::ios_base::app);
			out_file <<"\n"<<z3_solver<<"\n";
			out_file <<"\nz3_solver.get_model()\n";
			out_file <<"\n"<<m<<"\n";
			out_file.close();
#endif

		} else if (result == z3::unsat) {
			z3_solver.pop();
			cerr << "there is no data race!\n";
		} else {
			z3_solver.pop();
			cerr << "The result is unknown!\n";
		}
		z3_solver.pop();
		deleteReadWriteSet(record1, initializer_record1);
		deleteReadWriteSet(record2, initializer_record2);
	}
}

void Encode::buildRaceTraceFromLockSet() {
	trace->print(true);
	std::cerr << "trace->raceCandidateVar: " << trace->raceCandidateVar.size() << std::endl;
	vector<struct globalEvent> readGlobalSet;
	vector<struct globalEvent> writeGlobalSet;

	unsigned eventLen = trace->eventList.size();
//	std::cerr << "print the event inst made race happened\n";
	for (unsigned tid = 0; tid < eventLen; tid++) {
		std::vector<Event*> *thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0, threadLen = thread->size(); index < threadLen; index++) {
			Event *event = thread->at(index);
			if (event == NULL || event->eventType == Event::VIRTUAL
					|| event->eventType == Event::IGNORE)
				continue;
			if (trace->raceCandidateVar.count(event->varName) == 1) {
				if (event->isGlobal) {
//					event->inst->inst->dump();
					Event *preEvent = NULL;
					Event *postEvent = NULL;
					struct globalEvent globalTemp;

					globalTemp.event = event;
					for (int i = index - 1; i >= 0; i--) {
							if (thread->at(i)->eventName != event->eventName) {
								preEvent = thread->at(i);
								break;
							}
					}
					globalTemp.preEvent = preEvent;
					for (unsigned int j = index + 1; j < threadLen; j++) {
						if (thread->at(j)->eventName != event->eventName) {
							postEvent = thread->at(j);
							break;
						}
					}
					globalTemp.postEvent = postEvent;
					if (event->inst->inst->getOpcode() == Instruction::Store) {
						writeGlobalSet.push_back(globalTemp);
					}
					if (event->inst->inst->getOpcode() == Instruction::Load) {
						readGlobalSet.push_back(globalTemp);
					}
				}
			}
		}
	}
	std::cerr << "build race candidate from lock set: read size = " <<
			readGlobalSet.size() << " && write size = " << writeGlobalSet.size() << "\n";
	getRaceCandidate(readGlobalSet, writeGlobalSet);
}


void Encode::buildRaceTrace()
{
	vector<struct globalEvent> readGlobalSet;
	vector<struct globalEvent> writeGlobalSet;

	unsigned eventLen = trace->eventList.size();
	std::cerr << "eventLen = " << eventLen << "\n";
	for (unsigned tid = 0; tid < eventLen; tid++) {
		std::vector<Event*> *thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0, threadLen = thread->size(); index < threadLen; index++) {
			Event *event = thread->at(index);
			if (event == NULL || event->eventType == Event::VIRTUAL
					|| event->eventType == Event::IGNORE)
				continue;
			if (event->isGlobal) {
				Event *preEvent = NULL;
				Event *postEvent = NULL;
				event->inst->inst->dump();
				struct globalEvent globalTemp;

				globalTemp.event = event;
				for (int i = index - 1; i >= 0; i--) {
						if (thread->at(i)->eventName != event->eventName) {
							preEvent = thread->at(i);
							break;
						}
				}
				globalTemp.preEvent = preEvent;
				for (unsigned int j = index + 1; j < threadLen; j++) {
					if (thread->at(j)->eventName != event->eventName) {
							postEvent = thread->at(j);
							break;
						}
				}
				globalTemp.postEvent = postEvent;
				if (event->inst->inst->getOpcode() == Instruction::Store) {
					writeGlobalSet.push_back(globalTemp);
				}
				if (event->inst->inst->getOpcode() == Instruction::Load) {
					readGlobalSet.push_back(globalTemp);
				}
			}
		}
	}
	std::cerr << "read size = " << readGlobalSet.size() <<
			" && write size = " << writeGlobalSet.size() << "\n";
	getRaceCandidate(readGlobalSet, writeGlobalSet);
}


void Encode::getPossibleRaceTrace()
{
	std::cerr << "getPossibleRaceTrace\n";
//	buildRaceFormula();
//	addBrConstraint();
	buildPartialRaceFormula();
	buildRaceTraceFromLockSet();
//	buildRaceTrace();
}

void Encode::addBrConstraint(Event * event)
{
//	std::cerr << "ifFormula\n";
	expr eventExpr = z3_ctx.int_const(event->eventName.c_str());
	for (unsigned i = 0; i < ifFormula.size(); i++) {
//		std::cerr << ifFormula[i].second << std::endl;
		Event* temp = ifFormula[i].first;
		expr tempExpr = z3_ctx.int_const(temp->eventName.c_str());
		expr constraint = z3_ctx.bool_val(true);
		if (temp->threadId == event->threadId) {
			if (event->eventId > temp->eventId) {
				constraint = ifFormula[i].second;
			}
		} else {
			constraint = implies(tempExpr < eventExpr, ifFormula[i].second);
		}
		z3_solver.add(constraint);
	}
	//added assert formula cause long time solving.
	for (unsigned i = 0; i < assertFormula.size(); i++) {
//		std::cerr << ifFormula[i].second << std::endl;
		Event* temp = assertFormula[i].first;
		expr tempExpr = z3_ctx.int_const(temp->eventName.c_str());
		expr constraint = z3_ctx.bool_val(true);
		if (temp->threadId == event->threadId) {
			if (event->eventId > temp->eventId) {
				constraint = assertFormula[i].second;
			}
		} else {
			constraint = implies(tempExpr < eventExpr, assertFormula[i].second);
		}
		z3_solver.add(constraint);
	}
}


//true :: assert can't be violated. false :: assert can be violated.
bool Encode::verify() {
	cerr << "\nVerifying this trace......\n";
#if FORMULA_DEBUG
	stringstream ss;
	ss << "./output_info/" << "Trace" << trace->Id << ".z3expr" ;
	std::ofstream out_file(ss.str().c_str(),std::ios_base::out);
	out_file <<"\n"<<z3_solver<<"\n";
	out_file <<"\nifFormula\n";
	for (unsigned i = 0; i < ifFormula.size(); i++) {
		out_file << "Trace" << trace->Id << "#"
				<< ifFormula[i].first->inst->info->file << "#"
				<< ifFormula[i].first->inst->info->line << "#"
				<< ifFormula[i].first->eventName << "#"
				<< ifFormula[i].first->condition << "-"
				<< !(ifFormula[i].first->condition) << "\n";
		out_file << ifFormula[i].second << "\n";
	}
	out_file <<"\nassertFormula\n";
	for (unsigned i = 0; i < assertFormula.size(); i++) {
		out_file << "Trace" << trace->Id << "#"
				<< assertFormula[i].first->inst->info->file << "#"
				<< assertFormula[i].first->inst->info->line << "#"
				<< assertFormula[i].first->eventName << "#"
				<< assertFormula[i].first->condition << "-"
				<< !(assertFormula[i].first->condition) << "\n";
		out_file << assertFormula[i].second << "\n";
	}
	out_file.close();
#endif
	z3_solver.push();	//backtrack 1
	cerr << "\nThe number of assert: " << assertFormula.size() << "\n";
	for (unsigned i = 0; i < assertFormula.size(); i++) {
#if BRANCH_INFO
	stringstream ss;
	ss << "Trace" << trace->Id << "#"
//			<< assertFormula[i].first->inst->info->file << "#"
			<< assertFormula[i].first->inst->info->line << "#"
			<< assertFormula[i].first->eventName << "#"
			<< assertFormula[i].first->condition << "-"
			<< !(assertFormula[i].first->condition) << "assert_bug";
	cerr << "Verifying assert " << i+1 << " @" << ss.str() << ": ";
#endif
	z3_solver.push();	//backtrack point 2
	Event* curr = assertFormula[i].first;
	z3_solver.add(!assertFormula[i].second);
	for (unsigned j = 0; j < assertFormula.size(); j++) {
		if (j == i) {
			continue;
		}
		Event* temp = assertFormula[j].first;
		expr currIf = z3_ctx.int_const(curr->eventName.c_str());
		expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
		expr constraint = z3_ctx.bool_val(1);
		if (curr->threadId == temp->threadId) {
			if (curr->eventId > temp->eventId)
				constraint = assertFormula[j].second;
		} else
			constraint = implies(tempIf < currIf, assertFormula[j].second);
		z3_solver.add(constraint);
	}
	for (unsigned j = 0; j < ifFormula.size(); j++) {
		Event* temp = ifFormula[j].first;
		expr currIf = z3_ctx.int_const(curr->eventName.c_str());
		expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
		expr constraint = z3_ctx.bool_val(1);
		if (curr->threadId == temp->threadId) {
			if (curr->eventId > temp->eventId)
				constraint = ifFormula[j].second;
		} else
			constraint = implies(tempIf < currIf, ifFormula[j].second);
			z3_solver.add(constraint);
	}
	//statics
	struct timeval start, finish;
	gettimeofday(&start, NULL);

	check_result result = z3_solver.check();

	gettimeofday(&finish, NULL);
	double cost = (double) (finish.tv_sec * 1000000UL + finish.tv_usec
			- start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
	solvingCost += cost;
	solvingTimes++;
	stringstream output;
	if (result == z3::sat) {
		//should compute the prefix violating assert
		cerr << "Yes!\n";
		runtimeData.clearAllPrefix();
		//former :: replay the bug trace and erminate klee. later:: terminate klee directly
		if (true) {
			vector<Event*> vecEvent;
			computePrefix(vecEvent, assertFormula[i].first);
			Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint,
					ss.str());
			output << "./output_info/" << prefix->getName() << ".z3expr";
			runtimeData.addScheduleSet(prefix);
//		} else {
			cerr << "Assert Failure at "
					<< assertFormula[i].first->inst->info->file << ": "
					<< assertFormula[i].first->inst->info->line << "\n";
			runtimeData.satBranch++;
			runtimeData.satCost += cost;
#if FORMULA_DEBUG
			showPrefixInfo(prefix, assertFormula[i].first);
#endif

		}
#if FORMULA_DEBUG
		std::ofstream out_file(output.str().c_str(),std::ios_base::out|std::ios_base::app);
		out_file << "!assertFormula[i].second : " << !assertFormula[i].second << "\n";
		out_file <<"\n"<<z3_solver<<"\n";
		model m = z3_solver.get_model();
		out_file <<"\nz3_solver.get_model()\n";
		out_file <<"\n"<<m<<"\n";
		out_file.close();
#endif
//		logStatisticInfo();
			return false;
		} else if (result == z3::unknown) {
			cerr << "assert" << i << ": unknown!\n";
		} else if (result == z3::unsat) {
#if BRANCH_INFO
			cerr << "No!\n";
			runtimeData.unSatBranch++;
#endif
		}
		z3_solver.pop();	//backtrack point 2
	}
#if FORMULA_DEBUG
	showInitTrace();
#endif
	z3_solver.pop();	//backtrack 1
	cerr << "\nVerifying is over!\n";
	return true;
}

void Encode::check_if() {
	unsigned sum = 0, num = 0;
	unsigned size = ifFormula.size();
	cerr << "Sum of branches: " << size << "\n";
	for (unsigned i = 0; i < ifFormula.size(); i++) {
		num++;
#if BRANCH_INFO
//		cerr << ifFormula[i].second << "\n";
		stringstream ss;
		ss << "Trace" << trace->Id << "#"
//				<< ifFormula[i].first->inst->info->file << "#"
				<< ifFormula[i].first->inst->info->line << "#"
				<< ifFormula[i].first->eventName << "#"
				<< ifFormula[i].first->condition << "-"
				<< !(ifFormula[i].first->condition);
		cerr << "Verifying branch " << num << " @" << ss.str() << ": ";
#endif

		//create a backstracking point
		z3_solver.push();
		Event* curr = ifFormula[i].first;
		int branch = (long) ifFormula[i].first->inst->inst;
		//2: collect info from the two former executions.
		if (trace->Id >= 2) {
#if BRANCH_INFO
			cerr << "No!\n";
#endif
			continue;
		}

		z3_solver.add(!ifFormula[i].second);
		for (unsigned j = 0; j < ifFormula.size(); j++) {
			if (j == i) {
				continue;
			}
			Event* temp = ifFormula[j].first;
			expr currIf = z3_ctx.int_const(curr->eventName.c_str());
			expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
			expr constraint = z3_ctx.bool_val(1);
			if (curr->threadId == temp->threadId) {
				if (curr->eventId > temp->eventId)
					constraint = ifFormula[j].second;
			} else
				constraint = implies(tempIf < currIf, ifFormula[j].second);
			z3_solver.add(constraint);
		}
		//statics
		formulaNum = formulaNum + ifFormula.size() - 1;
		//solving
		check_result result;
		struct timeval start, finish;
		gettimeofday(&start, NULL);
		try {
			//statics
			result = z3_solver.check();
			solvingTimes++;
		} catch (z3::exception & ex) {
			std::cerr << "\nUnexpected error: " << ex << "\n";
			continue;
		}
		gettimeofday(&finish, NULL);
		double cost = (double) (finish.tv_sec * 1000000UL + finish.tv_usec
				- start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
		//
		stringstream output;
		if (result == z3::sat) {
			vector<Event*> vecEvent;
			computePrefix(vecEvent, ifFormula[i].first);
			Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint,
					ss.str());
			output << "./output_info/" << prefix->getName() << ".z3expr";
			//printf prefix to DIR output_info
			runtimeData.addScheduleSet(prefix);
			runtimeData.satBranch++;
			runtimeData.satCost += cost;
#if FORMULA_DEBUG
			showPrefixInfo(prefix, ifFormula[i].first);
#endif
		} else {
			runtimeData.unSatBranch++;
			runtimeData.unSatCost += cost;
		}

#if BRANCH_INFO
		if (result == z3::sat) {
			sum++;
			cerr << "Yes!\n";
#if FORMULA_DEBUG
		std::ofstream out_file(output.str().c_str(),std::ios_base::out|std::ios_base::app);
		out_file << "!ifFormula[i].second : " << !ifFormula[i].second << "\n";
		out_file <<"\n"<<z3_solver<<"\n";
		model m = z3_solver.get_model();
		out_file <<"\nz3_solver.get_model()\n";
		out_file <<"\n"<<m<<"\n";
		out_file.close();
#endif
		} else if (result == z3::unsat) {
			cerr << "No!\n";
		} else
			cerr << "Warning!\n";
#endif

		//backstracking
		z3_solver.pop();

	}

//	//print log
//	logStatisticInfo();
//
//	if (sum == 0)
//		cerr << "\nAll the branches can't be negated!\n";
//	else
//		cerr << "\nIn total, there are " << sum << "/" << size
//				<< " branches can be negated!\n";
}

void Encode::showInitTrace() {
	string ErrorInfo;
	stringstream output;
	output << "./output_info/" << "Trace" << trace->Id << ".bitcode" ;
	raw_fd_ostream out_to_file(output.str().c_str(), ErrorInfo, 0x0200);
	unsigned size = trace->path.size();
//bitcode
	for (unsigned i = 0; i < size; i++) {
		Event* currEvent = trace->path[i];
		if (trace->path[i]->inst->info->line == 0
				|| trace->path[i]->eventType != Event::NORMAL)
			continue;
		out_to_file << i << "---" << trace->path[i]->threadId << "---"
				<< trace->path[i]->eventName << "---"
				<< trace->path[i]->inst->inst->getParent()->getParent()->getName().str()
				<< "---" << trace->path[i]->inst->info->line << "---"
				<< trace->path[i]->condition << "---";
		trace->path[i]->inst->inst->print(out_to_file);
		if (currEvent->isGlobal) {
			out_to_file << "--" << currEvent->globalVarFullName << "=";
			string str = currEvent->globalVarFullName;
			if (str == ""){
				out_to_file << "\n";
				continue;
			}
		}
		if (currEvent->isLocal) {
			out_to_file << "--" << currEvent->varName << "=";
			string str = currEvent->varName;
		}
		out_to_file << "\n";
	}
//source code
	printSourceLine("./output_info/source_trace", trace->path);
}


void Encode::computePrefix(vector<Event*>& vecEvent, Event* ifEvent) {
	vector<struct Pair *> eventOrderPair;
//get the order of event
	map<string, expr>::iterator it = eventNameInZ3.find(ifEvent->eventName);
	assert(it != eventNameInZ3.end());
	model m = z3_solver.get_model();
	stringstream ss;
	ss << m.eval(it->second);
	long ifEventOrder = atoi(ss.str().c_str());
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0, size = thread->size(); index < size; index++) {
			if (thread->at(index)->eventType == Event::VIRTUAL)
				continue;

			it = eventNameInZ3.find(thread->at(index)->eventName);
			assert(it != eventNameInZ3.end());
			stringstream ss;
			ss << m.eval(it->second);
			long order = atoi(ss.str().c_str());
			//cut off segment behind the negated branch
			if (order > ifEventOrder)
				continue;
			if (order == ifEventOrder
					&& thread->at(index)->threadId != ifEvent->threadId)
				continue;
			if (thread->at(index)->eventName == ifEvent->eventName
					&& thread->at(index)->eventId > ifEvent->eventId)
				continue;
			//put the event to its position
			//
			Pair * pair = new Pair;				//should be deleted
			pair->order = order;
			pair->event = thread->at(index);
			eventOrderPair.push_back(pair);
		}
	}

//sort all events according to order
	unsigned size = eventOrderPair.size();
	for (unsigned i = 0; i < size - 1; i++) {
		for (unsigned j = 0; j < size - i - 1; j++) {
			if (eventOrderPair[j]->order > eventOrderPair[j + 1]->order) {
				Pair *temp = eventOrderPair[j];
				eventOrderPair[j] = eventOrderPair[j + 1];
				eventOrderPair[j + 1] = temp;
			}
		}
	}

//put the ordered events to vecEvent.
	for (unsigned i = 0; i < eventOrderPair.size(); i++) {
		//TODO: use a simple struct to log prefix
		vecEvent.push_back(eventOrderPair[i]->event);
		delete eventOrderPair[i];
	}
}

void Encode::showPrefixInfo(Prefix* prefix, Event* ifEvent) {
	try {
	vector<Event*>* orderedEventList = prefix->getEventList();
	unsigned size = orderedEventList->size();
	model m = z3_solver.get_model();
//print counterexample at bitcode
	string ErrorInfo;
	stringstream output;
	output << "./output_info/" << prefix->getName() << ".bitcode";
	raw_fd_ostream out_to_file(output.str().c_str(), ErrorInfo,
//			0x0200);
			raw_fd_ostream::BLACK);
	cerr << ErrorInfo;
//out_to_file << "threadId:   "<< "lineNum:    " << "source:" <<"\n";
//raw_fd_ostream out_to_file("./output_info/counterexample.txt", ErrorInfo, 2 & 0x0200);
	for (unsigned i = 0; i < size; i++) {
		Event* currEvent = orderedEventList->at(i);
		out_to_file << currEvent->threadId << "---" << currEvent->eventName
				<< "---"
				<< currEvent->inst->inst->getParent()->getParent()->getName().str()
				<< "---" << currEvent->inst->info->line << "---"
				<< currEvent->condition << "---";
		currEvent->inst->inst->print(out_to_file);
		if (currEvent->isGlobal) {
			out_to_file << "--" << currEvent->globalVarFullName << "=";
			string str = currEvent->globalVarFullName;
			if (str == ""){
				out_to_file << "\n";
				continue;
			}
			stringstream ss;
#if INT_ARITHMETIC
			ss << m.eval(z3_ctx.int_const(str.c_str()));
#else
			ss << m.eval(z3_ctx.bv_const(str.c_str(), BIT_WIDTH));	//just for
#endif
			out_to_file << ss.str();
		}
		if (currEvent->isLocal) {
			out_to_file << "--" << currEvent->varName << "=";
			string str = currEvent->varName;
			stringstream ss;
#if INT_ARITHMETIC
			ss << m.eval(z3_ctx.int_const(str.c_str()));
#else
			ss << m.eval(z3_ctx.bv_const(str.c_str(), BIT_WIDTH));
#endif
			out_to_file << ss.str();
		}
		out_to_file << "\n";
	}
	out_to_file.close();
//print source code
//	printSourceLine(filename, eventOrderPair);
	} catch (z3::exception &e) {
		std::cerr << "getModel error: " << e << std::endl;
	}
}

/*
 * called by showInitTrace to print initial trace
 */
void Encode::printSourceLine(string path, vector<Event *>& trace) {
	string output;
	string ErrorInfo;
	output = path + ".txt";
	raw_fd_ostream out_to_file(output.c_str(), ErrorInfo, 0x0200);
	out_to_file << "threadId  " << "lineNum   " << "function                 "
			<< "source" << "\n";
	unsigned preThreadId = 0, preCodeLine = 0;
	for (unsigned i = 0, size = trace.size(); i < size; i++) {
		if (trace[i]->eventType != Event::NORMAL)
			continue;
		if (trace[i]->inst->info->line == 0)
			continue;
		unsigned currCodeLine = trace[i]->inst->info->line;
		unsigned currThreadId = trace[i]->threadId;
		if (currThreadId == preThreadId && currCodeLine == preCodeLine)
			continue;
//		string fileName = trace[i]->codeDir + "/" + trace[i]->codeFile;
		string fileName = trace[i]->inst->info->file;
		string source = readLine(fileName, trace[i]->inst->info->line);
		if (source == "")
			assert(0 && "blank line");
		if (source == "{" || source == "}")
			continue;
		//write to file
		int len;
		stringstream ss;
		ss << currThreadId;
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 10 - len; k++)
			ss << " ";
		ss << currCodeLine;
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 20 - len; k++)
			ss << " ";
		ss << trace[i]->inst->inst->getParent()->getParent()->getName().str();
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 45 - len; k++)
			ss << " ";
		ss << source << "\n";
		out_to_file << ss.str();

		preThreadId = currThreadId;
		preCodeLine = currCodeLine;
	}
}

/*
 * called by showEventSequence to print counterexample
 */
void Encode::printSourceLine(string path,
		vector<struct Pair *>& eventIndexPair) {
	string output;
	string ErrorInfo;
	output = "./output_info/" + path + ".source";
	raw_fd_ostream out_to_file(output.c_str(), ErrorInfo, 0x0200);
	out_to_file << "threadId  " << "lineNum   " << "function                 "
			<< "source" << "\n";

	unsigned preThreadId = 0, preCodeLine = 0;
	for (unsigned i = 0, size = eventIndexPair.size(); i < size; i++) {

		if (eventIndexPair[i]->event->eventType != Event::NORMAL)
			continue;
		if (eventIndexPair[i]->event->inst->info->line == 0)
			continue;
		unsigned currCodeLine = eventIndexPair[i]->event->inst->info->line;
		unsigned currThreadId = eventIndexPair[i]->event->threadId;
		if (currThreadId == preThreadId && currCodeLine == preCodeLine)
			continue;
//		string fileName = eventIndexPair[i]->event->codeDir + "/"
//				+ eventIndexPair[i]->event->codeFile;
		string fileName = eventIndexPair[i]->event->inst->info->file;
		string source = readLine(fileName,
				eventIndexPair[i]->event->inst->info->line);
		if (source == "{" || source == "}")
			continue;
		//write to file
		int len;
		stringstream ss;
		ss << currThreadId;
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 10 - len; k++)
			ss << " ";
		ss << currCodeLine;
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 20 - len; k++)
			ss << " ";
		ss
				<< eventIndexPair[i]->event->inst->inst->getParent()->getParent()->getName().str();
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 45 - len; k++)
			ss << " ";
		ss << source << "\n";
		out_to_file << ss.str();
		preThreadId = currThreadId;
		preCodeLine = currCodeLine;
	}
}

bool Encode::isAssert(string filename, unsigned line) {
	char source[BUFFERSIZE];
	ifstream ifile(filename.c_str());
	if (!ifile.is_open())
		assert(0 && "open file error");
	unsigned i = 0;
	while (i != line) {
		ifile.getline(source, BUFFERSIZE);
		i += 1;
	}
	ifile.close();
	string s(source);
	return s.find("assert", 0) != string::npos;
}

string Encode::readLine(string filename, unsigned line) {
	char source[BUFFERSIZE];
	ifstream ifile(filename.c_str());
	if (!ifile.is_open())
		assert(0 && "open file error");
	unsigned i = 0;
	while (i != line) {
		ifile.getline(source, BUFFERSIZE);
		i += 1;
	}
	ifile.close();
	return stringTrim(source);
}

string Encode::stringTrim(char * source) {
	string ret;
	char dest[BUFFERSIZE];
	int k = 0;
	int s = 0, e = 0;
	int len = strlen(source);
	for (int i = 0; i < len; i++) {
		if (!isspace(source[i])) {
			s = i;
			break;
		}
	}
	for (int i = (len - 1); i >= 0; i--) {
		if (!isspace(source[i])) {
			e = i;
			break;
		}
	}
	for (int i = s; i <= e; i++) {
		dest[k++] = source[i];
	}
	dest[k] = '\0';
	ret = dest;
	return ret;
}
void Encode::logStatisticInfo() {
	unsigned threadNumber = 0;
	unsigned instNumber = 0;
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		threadNumber++;
		instNumber += thread->size();
	}
	unsigned lockNumber = trace->all_lock_unlock.size();
	unsigned lockPairNumber = 0;
	std::map<std::string, std::vector<LockPair *> >::iterator it =
			trace->all_lock_unlock.begin();
	for (; it != trace->all_lock_unlock.end(); it++) {
		lockPairNumber += it->second.size();
	}
	unsigned signalNumber = trace->all_signal.size();
	unsigned waitNumber = trace->all_wait.size();
	unsigned sharedVarNumber = trace->global_variable_final.size();
	unsigned readNumber = trace->readSet.size();
	unsigned writeNumber = trace->writeSet.size();
	string ErrorInfo;
	raw_fd_ostream out("./output_info/statistic.info", ErrorInfo, 0x0200);
	out << "#Threads:" << threadNumber << "\n";
	out << "#Instructions: " << instNumber << "\n";
	out << "#Locks: " << lockNumber << "\n";
	out << "#Lock/Unlock Pairs: " << lockPairNumber << "\n";
	out << "#Signal/Wait: " << signalNumber << "/" << waitNumber << "\n";
	out << "#Shared Variables: " << sharedVarNumber << "\n";
	out << "#Read/Write of shared points: " << readNumber << "/" << writeNumber
			<< "\n";
//	out << "#Constaints: " << constaintNumber << "\n";
	stringstream ss;
	ss << solvingCost;
	out << "Solving Cost: " << ss.str() << " s\n";
}


std::string Encode::getVarName(ref<klee::Expr> value) {
//	std::cerr << "getVarName : " << value << "\n";
	std::stringstream varName;
	varName.str("");
	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		return varName.str();
	}
	std::string globalVarFullName = revalue->updates.root->name;
	unsigned int i = 0;
	while ((globalVarFullName.at(i) != 'S') && (globalVarFullName.at(i) != 'L')) {
		varName << globalVarFullName.at(i);
		i++;
	}
	return varName.str();
}

std::string Encode::getFullName(ref<klee::Expr> value) {

	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		assert( 0 && "getFullName");
	}
	std::string globalVarFullName = revalue->updates.root->name;
	return globalVarFullName;
}


void Encode::resolveGlobalVarName(ref<klee::Expr> value)
{
	if (value->getKind() == Expr::Read) {
		std::string varName = getVarName(value);
		if (relatedVarName.find(varName) == relatedVarName.end()) {
			relatedVarName.insert(varName);
		}
		return ;
	} else {
		unsigned kidsNum = value->getNumKids();
		if (kidsNum == 2 && value->getKid(0) == value->getKid(1)) {
			resolveGlobalVarName(value->getKid(0));
		} else {
			for (unsigned int i = 0; i < kidsNum; i++) {
				resolveGlobalVarName(value->getKid(i));
			}
		}
	}
}

void Encode::getGlobalFirstOrderRelated(Trace * trace)
{
	std::vector<ref<klee::Expr> > &storeSymbolicExpr = trace->storeSymbolicExpr;
	std::string varName = "";
	for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(), ie =
			storeSymbolicExpr.end(); it != ie; ++it) {

		varName = getVarName(it->get()->getKid(1));
		trace->remainingExpr.push_back(*it);
		trace->remainingExprVarName.push_back(varName);
		relatedVarName.clear();
		resolveGlobalVarName(it->get()->getKid(0));
		if (trace->globalVarFirstOrderRelated.find(varName) ==
				trace->globalVarFirstOrderRelated.end()) {
			trace->globalVarFirstOrderRelated.insert(make_pair(varName, relatedVarName));
		} else {
			std::set<std::string> &temp = trace->globalVarFirstOrderRelated.find(varName)->second;
			temp.insert(relatedVarName.begin(), relatedVarName.end());
		}
	}
}

void Encode::getUsefulGlobalVar(Trace * trace, std::string str)
{
	trace->usefulGlobalVar.insert(str);
	std::map<std::string, std::set<std::string> >::iterator it =
			trace->globalVarFirstOrderRelated.find(str);
	if (it != trace->globalVarFirstOrderRelated.end()) {
		std::set<std::string> &temp = it->second;
		std::set<std::string>::iterator it = temp.begin(), ie = temp.end();
		for (; it != ie; it++) {
			if (trace->usefulGlobalVar.find(*it) != trace->usefulGlobalVar.end()) {
				getUsefulGlobalVar(trace, *it);
			}
		}
	}
}

void Encode::getPathCondition(Trace *trace)
{
	ifFormula.clear();
	std::vector<ref<klee::Expr> > &kQueryExpr = trace->kQueryExpr;
	kQueryExpr.clear();
//	std::vector<ref<klee::Expr> > testExpr;
	for (std::set<std::string>::iterator it = trace->usefulGlobalVar.begin(),
			ie = trace->usefulGlobalVar.end(); it != ie; it++) {
		std::string varName = *it;
		std::vector<ref<Expr> >::iterator itt = trace->remainingExpr.begin();
		for (std::vector<std::string>::iterator rit = trace->remainingExprVarName.begin(),
				rie = trace->remainingExprVarName.end(); rit != rie; rit++, itt++) {
			if (varName == *rit) {
				kQueryExpr.push_back(*itt);
			}
		}
	}
//	std::cerr << "path Condition is \n";
//	for (std::vector<ref<klee::Expr> >::iterator tit = kQueryExpr.begin(), tie = kQueryExpr.end();
//			tit != tie; tit++) {
//		std::cerr << *tit << std::endl;
//	}
}
void Encode::getUsefulReadWriteSet(Trace* trace, std::string str)
{
	trace->usefulGlobalVar.clear();
	getUsefulGlobalVar(trace, str);
	std::map<std::string, std::vector<Event *> > usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator it = readSet.begin(),
			ie = readSet.end(); it != ie; it++) {
		if (trace->usefulGlobalVar.find(it->first) != trace->usefulGlobalVar.end()) {
//			std::cerr << "read it->first = " << it->first << std::endl;
			usefulReadSet.insert(*it);
		}
	}
//	std::cerr << "usefulReadSet size = " << usefulReadSet.size() << std::endl;
	readSet.clear();
	readSet.insert(usefulReadSet.begin(), usefulReadSet.end());
	std::map<std::string, std::vector<Event *> > usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator it = writeSet.begin(),
			ie = writeSet.end(); it != ie; it++) {
		if (trace->usefulGlobalVar.find(it->first) != trace->usefulGlobalVar.end()) {
//			std::cerr << "write it->first = " << it->first << std::endl;
			usefulWriteSet.insert(*it);
		}
	}
//	std::cerr << "usefulWriteSet size = " << usefulWriteSet.size() << std::endl;
	writeSet.clear();
	writeSet.insert(usefulWriteSet.begin(), usefulWriteSet.end());

	std::map<std::string, llvm::Constant*> usefulGlobal_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	usefulGlobal_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		if (trace->usefulGlobalVar.find(nit->first) != trace->usefulGlobalVar.end()) {
//			std::cerr << "global it->first = " << nit->first << std::endl;
			usefulGlobal_variable_initializer.insert(*nit);
		}
	}
//	std::cerr << "usefulGlobal_variable_initializer size = " << usefulGlobal_variable_initializer.size() << std::endl;
	global_variable_initializer.clear();
	global_variable_initializer.insert(usefulGlobal_variable_initializer.begin(),
			usefulGlobal_variable_initializer.end());

//	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
//			currentEvent != endEvent; currentEvent++) {
//		if ((*currentEvent)->isGlobal == true) {
//			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
//					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
//				if (trace->usefulGlobalVar.find((*currentEvent)->varName) == trace->usefulGlobalVar.end()) {
//					(*currentEvent)->isGlobal = false;
//				}
//			}
//		}
//	}
}


void Encode::getUsefulLockPair(Trace *trace)
{
	std::map<std::string, std::vector<LockPair *> > usefulLockPair;
	std::set<std::string>::iterator uit = trace->usefulGlobalVar.begin(),
			uie = trace->usefulGlobalVar.end();
	for (; uit != uie; uit++) {
		std::map<std::string, std::set<std::string> >::iterator git =
				trace->globalVarRelatedLock.find(*uit);
		if (git != trace->globalVarRelatedLock.end()) {
			std::set<std::string>::iterator lit = git->second.begin(), lie = git->second.end();
			for (; lit != lie; lit++) {
				usefulLockPair.insert(make_pair(*lit, trace->all_lock_unlock.find(*lit)->second));
			}
		}
	}
	std::cerr << "usefulLockPair size = " << usefulLockPair.size() << std::endl;
	trace->all_lock_unlock.clear();
	trace->all_lock_unlock.insert(usefulLockPair.begin(), usefulLockPair.end());
}


void Encode::buildInitValueFormula() {
//for global initializer
#if FORMULA_DEBUG
	cerr << "\nGlobal var initial value:\n";
	cerr << "\nGlobal var initial size: " << trace->global_variable_initializer.size() << "\n";
#endif
	std::map<std::string, llvm::Constant*>::iterator gvi =
			trace->global_variable_initializer.begin();

	std::cerr << "global_variable size = " <<
			trace->global_variable_initializer.size() << std::endl;
	for (; gvi != trace->global_variable_initializer.end(); gvi++) {
		//bitwidth may introduce bug!!!
		const Type *type = gvi->second->getType();
		const z3::sort varType(llvmTy_to_z3Ty(type));
		string str = gvi->first + "_Init";
		expr lhs = z3_ctx.constant(str.c_str(), varType);
		expr rhs = buildExprForConstantValue(gvi->second, false, "");
		z3_solver.add(lhs == rhs);

#if FORMULA_DEBUG
		cerr << (lhs == rhs) << "\n";
#endif
	}
	//statics
	formulaNum += trace->global_variable_initializer.size();
}

void Encode::buildOutputFormula() {
//for global var at last
//need to choose manually
#if FORMULA_DEBUG
	cerr << "\nGlobal var final value:\n";
#endif
	std::map<std::string, llvm::Constant*>::iterator gvl =
			trace->global_variable_final.begin();
	for (; gvl != trace->global_variable_final.end(); gvl++) {
		const Type *type = gvl->second->getType();
		const z3::sort varType(llvmTy_to_z3Ty(type));
		string str = gvl->first + "_Final";
		expr lhs = z3_ctx.constant(str.c_str(), varType);
		expr rhs = buildExprForConstantValue(gvl->second, false, "");
		expr finalValue = (lhs == rhs);
		expr constrait = z3_ctx.bool_val(1);

		vector<Event*> maybeRead;
		map<int, map<string, Event*> >::iterator atlw =
				allThreadLastWrite.begin();
		for (; atlw != allThreadLastWrite.end(); atlw++) {
			map<string, Event*>::iterator it = atlw->second.find(gvl->first);
			if (it != atlw->second.end()) {
				maybeRead.push_back(it->second);
			}
		}
		if (maybeRead.size() == 0) {	//be equal with initial value!
			string str = gvl->first + "_Init";
			expr init = z3_ctx.constant(str.c_str(), varType);
			constrait = (lhs == init);
		} else {	//be equal with the last write in some threads
			vector<expr> allReads;
			for (unsigned i = 0; i < maybeRead.size(); i++) {
				//build the equation
				expr write = z3_ctx.constant(
						maybeRead[i]->globalVarFullName.c_str(), varType);//used write event
				expr eq = (lhs == write);
				//build the constrait of equation
				expr writeOrder = z3_ctx.int_const(
						maybeRead[i]->eventName.c_str());
				vector<expr> beforeRelation;
				for (unsigned j = 0; j < maybeRead.size(); j++) {
					if (j == i)
						continue;
					expr otherWriteOrder = z3_ctx.int_const(
							maybeRead[j]->eventName.c_str());
					expr temp = (otherWriteOrder < writeOrder);
					beforeRelation.push_back(temp);
				}
				expr tmp = makeExprsAnd(beforeRelation);
				allReads.push_back(eq && tmp);
			}
			constrait = makeExprsOr(allReads);
		}

		pair<expr, expr> temp = make_pair(finalValue, constrait);
#if FORMULA_DEBUG
		cerr << "\n" << finalValue << "-------" << constrait;
#endif
		globalOutputFormula.push_back(temp);
	}
}

void Encode::markLatestWriteForGlobalVar() {
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0; index < thread->size(); index++) {
			Event* event = thread->at(index);
			if (event->isGlobal) {
				Instruction *I = event->inst->inst;
				if (StoreInst::classof(I)) { //write
					latestWriteOneThread[event->varName] = event;
				} else if (!event->implicitGlobalVar.empty()
						&& CallInst::classof(I)) {
					for (unsigned i = 0; i < event->implicitGlobalVar.size();
							i++) {
						string curr = event->implicitGlobalVar[i];
						string varName = curr.substr(0, curr.find('S', 0));
						latestWriteOneThread[varName] = event;
					}
				} else { //read
					Event * writeEvent;
					map<string, Event *>::iterator it;
					it = latestWriteOneThread.find(event->varName);
					if (it != latestWriteOneThread.end()) {
						writeEvent = it->second;
					} else {
						writeEvent = NULL;
					}
					event->latestWrite = writeEvent;
				}
			}
		}
		//post operations
		allThreadLastWrite[tid] = latestWriteOneThread;
		latestWriteOneThread.clear();
	}
}

void Encode::buildPathCondition() {
#if FORMULA_DEBUG
	cerr << "\nBasicFormula:\n";
#endif

	KQuery2Z3 * kq = new KQuery2Z3(z3_ctx);
	unsigned int totalExpr = trace->kQueryExpr.size();
	for (unsigned int i = 0; i < totalExpr; i++) {
//		std::cerr << trace->kQueryExpr[i] << std::endl;
		z3::expr temp = kq->getZ3Expr(trace->kQueryExpr[i]);
		z3_solver.add(temp);
#if FORMULA_DEBUG
	cerr << temp << "\n";
#endif
	}
	//special handle for statement br
	unsigned int totalAssertEvent = trace->assertEvent.size();
	unsigned int totalBrEvent = trace->brEvent.size();
	unsigned int totalAssertSymbolic = trace->assertSymbolicExpr.size();

	assert(
			totalAssertEvent == totalAssertSymbolic
					&& "the number of brEvent is not equal to brSymbolic");
	Event * event = NULL;
	z3::expr res = z3_ctx.bool_val(true);
	for (unsigned int i = 0; i < totalAssertEvent; i++) {
		event = trace->assertEvent[i];
//		cerr << "asert : " << trace->assertSymbolicExpr[i] <<"\n";
		res = kq->getZ3Expr(trace->assertSymbolicExpr[i]);
//		string fileName = event->inst->info->file;
		unsigned line = event->inst->info->line;
		if (line != 0)
			assertFormula.push_back(make_pair(event, res));
//		else
//			ifFormula.push_back(make_pair(event, res));

	}
	for (unsigned int i = 0; i < totalBrEvent; i++) {
		event = trace->brEvent[i];
		res = kq->getZ3Expr(trace->brSymbolicExpr[i]);
		if(event->isConditionIns == true){
//			cerr << "br : " << trace->brSymbolicExpr[i] <<"\n";
//			event->inst->inst->dump();
//			string fileName = event->inst->info->file;
//			unsigned line = event->inst->info->line;
//			cerr << "fileName : " << fileName <<" line : " << line << "\n";
			ifFormula.push_back(make_pair(event, res));
//			cerr << "event name : " << ifFormula[i].first->eventName << "\n";
//			cerr << "constraint : " << ifFormula[i].second << "\n";
		}else if(event->isConditionIns == false){
			z3_solver.add(res);
		}
	}

	unsigned int totalRwExpr = trace->rwSymbolicExpr.size();
	for (unsigned int i = 0; i < totalRwExpr; i++) {
		event = trace->rwEvent[i];
		res = kq->getZ3Expr(trace->rwSymbolicExpr[i]);
		rwFormula.push_back(make_pair(event, res));
//		cerr << "rwSymbolicExpr : " << res << "\n";
	}
}

void Encode::rebuildPathCondition()
{
	KQuery2Z3 * kq = new KQuery2Z3(z3_ctx);
	unsigned int totalExpr = trace->kQueryExpr.size();
	for (unsigned int i = 0; i < totalExpr; i++) {
		z3::expr temp = kq->getZ3Expr(trace->kQueryExpr[i]);
		z3_solver.add(temp);
#if FORMULA_DEBUG
	cerr << temp << "\n";
#endif
	}
	Event * event = NULL;
	unsigned int totalBrEvent = trace->brEvent.size();
	unsigned int totalAssertEvent = trace->assertEvent.size();
	for (unsigned int i = 0; i < totalBrEvent; i++) {
		relatedVarName.clear();
		resolveGlobalVarName(trace->brSymbolicExpr[i]);
		event = trace->brEvent[i];
		std::set<std::string>::iterator it = relatedVarName.begin(),
				ie = relatedVarName.end();
		for (; it != ie; it++) {
			if (trace->usefulGlobalVar.find(*it) != trace->usefulGlobalVar.end() &&
					event->isConditionIns == true) {
				ifFormula.push_back(make_pair(event, kq->getZ3Expr(trace->brSymbolicExpr[i])));
				break;
			}
		}
	}
	for (unsigned i = 0; i < totalAssertEvent; i++) {
		event = trace->assertEvent[i];
		if (event->inst->info->line != 0) {
			ifFormula.push_back(make_pair(event, kq->getZ3Expr(trace->assertSymbolicExpr[i])));
		}
	}
}

expr Encode::buildExprForConstantValue(Value *V, bool isLeft,
		string currInstPrefix) {
	assert(V && "V is null!");
	expr ret = z3_ctx.bool_val(1);
//llvm type to z3 type, except load and store inst which contain pointer
	const z3::sort varType(llvmTy_to_z3Ty(V->getType()));
//
	if (ConstantInt *ci = dyn_cast<ConstantInt>(V)) {
		int val = ci->getSExtValue();
		unsigned num_bit = ((IntegerType *) V->getType())->getBitWidth();
		if (num_bit == 1)
			ret = z3_ctx.bool_val(val);
		else
#if INT_ARITHMETIC
			ret = z3_ctx.int_val(val);
#else
			ret = z3_ctx.bv_val(val, BIT_WIDTH);
#endif

	} else if (ConstantFP *cf = dyn_cast<ConstantFP>(V)) {
		double val;
		APFloat apf = cf->getValueAPF();
		const struct llvm::fltSemantics & semantics = apf.getSemantics();
		if (apf.semanticsPrecision(semantics) == 53)
			val = apf.convertToDouble();
		else if (apf.semanticsPrecision(semantics) == 24)
			val = apf.convertToFloat();
		else
			assert(0 && "Wrong with Float Type!");

//		cerr << setiosflags(ios::fixed) << val << "\n";
		char s[200];
		sprintf(s, "%f", val);
		ret = z3_ctx.real_val(s);
	} else if (dyn_cast<ConstantPointerNull>(V)) {
		//%cmp = icmp eq %struct.bounded_buf_tag* %tmp, null
#if INT_ARITHMETIC
		ret = z3_ctx.int_val(0);
#else
		ret = z3_ctx.bv_val(0, BIT_WIDTH);
#endif

	} else if (llvm::ConstantExpr* constantExpr = dyn_cast<llvm::ConstantExpr>(
			V)) {
		Instruction* inst = constantExpr->getAsInstruction();
		if (IntToPtrInst::classof(inst)) {
			//cmp26 = icmp eq i8* %tmp19, inttoptr (i32 -1 to i8*)
			IntToPtrInst * ptrtoint = dyn_cast<IntToPtrInst>(inst);
			ConstantInt * ci = dyn_cast<ConstantInt>(ptrtoint->getOperand(0));
			assert(ci && "Impossible!");
			int val = ci->getValue().getLimitedValue();
#if INT_ARITHMETIC
			ret = z3_ctx.int_val(val);
#else
			ret = z3_ctx.bv_val(val, BIT_WIDTH);	//to pointer, the default is 32bit.
#endif

		} else {
			assert(0 && "unknown type of Value:1");
		}
		delete inst;		//must be done
	} else {
		assert(0 && "unknown type of Value:2");
	}

	return ret;
}


/*
z3::sort Encode::llvmTy_to_z3Ty(const Type *typ) {
	switch (typ->getTypeID()) {
	case Type::VoidTyID:
		assert(0 && "void return value!");
		break;
	case Type::HalfTyID:
	case Type::FloatTyID:
	case Type::DoubleTyID:
		return z3_ctx.real_sort();
	case Type::X86_FP80TyID:
		assert(0 && "couldn't handle X86_FP80 type!");
		break;
	case Type::FP128TyID:
		assert(0 && "couldn't handle FP128 type!");
		break;
	case Type::PPC_FP128TyID:
		assert(0 && "couldn't handle PPC_FP128 type!");
		break;
	case Type::LabelTyID:
		assert(0 && "couldn't handle Label type!");
		break;
	case Type::MetadataTyID:
		assert(0 && "couldn't handle Metadata type!");
		break;
	case Type::X86_MMXTyID:
		assert(0 && "couldn't handle X86_MMX type!");
		break;
	case Type::IntegerTyID: {
		unsigned num_bit = ((IntegerType *) typ)->getBitWidth();
		if (num_bit == 1) {
			return z3_ctx.bool_sort();;
		} else {
			return z3_ctx.bv_sort(BIT_WIDTH);
		}
		break;
	}
	case Type::FunctionTyID:
		assert(0 && "couldn't handle Function type!");
		break;
	case Type::StructTyID:
		return z3_ctx.bv_sort(BIT_WIDTH);
		break;
	case Type::ArrayTyID:
		assert(0 && "couldn't handle Array type!");             //must
		break;
	case Type::PointerTyID:
		return z3_ctx.bv_sort(BIT_WIDTH);
	case Type::VectorTyID:
		assert(0 && "couldn't handle Vector type!");
		break;
	case Type::NumTypeIDs:
		assert(0 && "couldn't handle NumType type!");
		break;
		//case Type::LastPrimitiveTyID: assert(0); break;
		//case Type::FirstDerivedTyID: assert(0); break;
	default:
		assert(0 && "No such type!");
		break;
	}

	return z3_ctx.bv_sort(BIT_WIDTH);
}        //
*/

z3::sort Encode::llvmTy_to_z3Ty(const Type *typ) {
	switch (typ->getTypeID()) {
	case Type::VoidTyID:
		assert(0 && "void return value!");
		break;
	case Type::HalfTyID:
	case Type::FloatTyID:
	case Type::DoubleTyID:
		return z3_ctx.real_sort();
	case Type::X86_FP80TyID:
		assert(0 && "couldn't handle X86_FP80 type!");
		break;
	case Type::FP128TyID:
		assert(0 && "couldn't handle FP128 type!");
		break;
	case Type::PPC_FP128TyID:
		assert(0 && "couldn't handle PPC_FP128 type!");
		break;
	case Type::LabelTyID:
		assert(0 && "couldn't handle Label type!");
		break;
	case Type::MetadataTyID:
		assert(0 && "couldn't handle Metadata type!");
		break;
	case Type::X86_MMXTyID:
		assert(0 && "couldn't handle X86_MMX type!");
		break;
	case Type::IntegerTyID: {
		unsigned num_bit = ((IntegerType *) typ)->getBitWidth();
		if (num_bit == 1) {
			return z3_ctx.bool_sort();;
		} else {
#if INT_ARITHMETIC
			return z3_ctx.int_sort();
#else
			return z3_ctx.bv_sort(BIT_WIDTH);
#endif

		}
		break;
	}
	case Type::FunctionTyID:
		assert(0 && "couldn't handle Function type!");
		break;
	case Type::StructTyID:
#if INT_ARITHMETIC
		return z3_ctx.int_sort();
#else
		return z3_ctx.bv_sort(BIT_WIDTH);
#endif
		break;
	case Type::ArrayTyID:
		assert(0 && "couldn't handle Array type!");             //must
		break;
	case Type::PointerTyID:
#if INT_ARITHMETIC
		return z3_ctx.int_sort();
#else
		return z3_ctx.bv_sort(BIT_WIDTH);
#endif
	case Type::VectorTyID:
		assert(0 && "couldn't handle Vector type!");
		break;
	case Type::NumTypeIDs:
		assert(0 && "couldn't handle NumType type!");
		break;
		//case Type::LastPrimitiveTyID: assert(0); break;
		//case Type::FirstDerivedTyID: assert(0); break;
	default:
		assert(0 && "No such type!");
		break;
	}
#if INT_ARITHMETIC
	return z3_ctx.int_sort();
#else
	return z3_ctx.bv_sort(BIT_WIDTH);
#endif

}        //


void Encode::rebuildMemoryModel()
{
#if FORMULA_DEBUG
	cerr << "\nMemoryModelFormula:\n";
#endif
	z3_solver.add(z3_ctx.int_const("E_INIT") == 0);
	//statics
	formulaNum++;
//level: 0 bitcode; 1 source code; 2 block
//	controlGranularity(2);
	int uniqueNum = 1;
	repartitionGranularity(uniqueNum);
	std::cerr << "uniqueNum = " << uniqueNum << std::endl;
//
//initial and final
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		//initial
		Event* firstEvent = thread->at(0);
		expr init = z3_ctx.int_const("E_INIT");
		expr firstEventExpr = z3_ctx.int_const(firstEvent->eventName.c_str());
		expr temp1 = (init < firstEventExpr);
#if FORMULA_DEBUG
		cerr << temp1 << "\n";
#endif
		z3_solver.add(temp1);

		//final
		Event* finalEvent = thread->back();
		expr final = z3_ctx.int_const("E_FINAL");
		expr finalEventExpr = z3_ctx.int_const(finalEvent->eventName.c_str());
		expr temp2 = (finalEventExpr < final);
#if FORMULA_DEBUG
		cerr << temp2 << "\n";
#endif
		z3_solver.add(temp2);
		//statics
		formulaNum += 2;
	}

//normal events
	/*
	int uniqueEvent = 1;
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0, size = thread->size(); index < size - 1;
				index++) {
			Event* pre = thread->at(index);
			Event* post = thread->at(index + 1);
			//by clustering
			if (pre->eventName == post->eventName)
				continue;
			uniqueEvent++;
			expr preExpr = z3_ctx.int_const(pre->eventName.c_str());
			expr postExpr = z3_ctx.int_const(post->eventName.c_str());
			expr temp = (preExpr < postExpr);
#if FORMULA_DEBUG
			cerr << temp << "\n";
#endif
			z3_solver.add(temp);
			//statics
			formulaNum++;

			//eventNameInZ3 will be used at check_if
			eventNameInZ3.insert(
					map<string, expr>::value_type(pre->eventName, preExpr));
			eventNameInZ3.insert(
					map<string, expr>::value_type(post->eventName, postExpr));
		}
	}
	*/
	z3_solver.add(
			z3_ctx.int_const("E_FINAL") == z3_ctx.int_val(uniqueNum) + 100);
	//statics
	formulaNum++;
}

void Encode::buildMemoryModelFormula() {
#if FORMULA_DEBUG
	cerr << "\nMemoryModelFormula:\n";
#endif
	z3_solver.add(z3_ctx.int_const("E_INIT") == 0);
	//statics
	formulaNum++;
//level: 0 bitcode; 1 source code; 2 block
	controlGranularity(2);
//
//initial and final
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		//initial
		Event* firstEvent = thread->at(0);
		expr init = z3_ctx.int_const("E_INIT");
		expr firstEventExpr = z3_ctx.int_const(firstEvent->eventName.c_str());
		expr temp1 = (init < firstEventExpr);
#if FORMULA_DEBUG
		cerr << temp1 << "\n";
#endif
		z3_solver.add(temp1);

		//final
		Event* finalEvent = thread->back();
		expr final = z3_ctx.int_const("E_FINAL");
		expr finalEventExpr = z3_ctx.int_const(finalEvent->eventName.c_str());
		expr temp2 = (finalEventExpr < final);
#if FORMULA_DEBUG
		cerr << temp2 << "\n";
#endif
		z3_solver.add(temp2);
		//statics
		formulaNum += 2;
	}

//normal events
	int uniqueEvent = 1;
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0, size = thread->size(); index < size - 1;
				index++) {
			Event* pre = thread->at(index);
			Event* post = thread->at(index + 1);
			//by clustering
			if (pre->eventName == post->eventName)
				continue;
			uniqueEvent++;
			expr preExpr = z3_ctx.int_const(pre->eventName.c_str());
			expr postExpr = z3_ctx.int_const(post->eventName.c_str());
			expr temp = (preExpr < postExpr);
#if FORMULA_DEBUG
			cerr << temp << "\n";
#endif
			z3_solver.add(temp);
			//statics
			formulaNum++;

			//eventNameInZ3 will be used at check_if
			eventNameInZ3.insert(
					map<string, expr>::value_type(pre->eventName, preExpr));
			eventNameInZ3.insert(
					map<string, expr>::value_type(post->eventName, postExpr));
		}
	}
	z3_solver.add(
			z3_ctx.int_const("E_FINAL") == z3_ctx.int_val(uniqueEvent) + 100);
	//statics
	formulaNum++;
}

void Encode::repartitionGranularity(int &uniqueNum)
{
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		Event* pre = thread->at(0);
		InstType preInstType = getInstOpType(pre);
		pre->preEventName = "Init";
		string preEventName = pre->preEventName;
		expr preExpr = z3_ctx.int_const(pre->eventName.c_str());
		uniqueNum++;

		for (unsigned index = 1, size = thread->size(); index < size;
				index++) {
			Event* curr = thread->at(index);
			InstType currInstType = getInstOpType(curr);

			//debug
//				curr->inst->inst->print(cerr);
//				cerr << "\n";
//				if (currInstType == NormalOp)
//					cerr << "NormalOp!\n";
//				else if (currInstType == GlobalVarOp)
//					cerr << "GlobalVarOp!\n";
//				else if (currInstType == ThreadOp)
//					cerr << "ThreadOp!\n";

			if (preInstType == NormalOp) {
//				curr->eventName = preEventName;
				expr currExpr = z3_ctx.int_const(curr->eventName.c_str());
				z3_solver.add(preExpr == currExpr);
				curr->preEventName = preEventName;
			} else {
//				preEventName = curr->eventName;
				expr tempExpr = z3_ctx.int_const(curr->eventName.c_str());
				z3_solver.add( (preExpr < tempExpr) );
				curr->preEventName = pre->eventName;
				preEventName = pre->eventName;
				preExpr = tempExpr;
				pre = curr;
				uniqueNum++;
			}
			preInstType = currInstType;
		}
//		for (unsigned i = 0; i < thread->size(); i++) {
//			std::cerr << "eventName = " << thread->at(i)->eventName <<
//				", preEventName = " << thread->at(i)->preEventName << std::endl;
//		}
		Event *tempPost = thread->at(thread->size() - 1);
		tempPost->postEventName = "Over";
		string postEventName = tempPost->postEventName;
		std::vector<Event*>::size_type i = thread->size() - 2;
		for (; i > 0; i--) {
			Event *curr = thread->at(i);
			if (tempPost->preEventName == curr->preEventName) {
				curr->postEventName = postEventName;
			} else {
				curr->postEventName = tempPost->eventName;
				postEventName = tempPost->eventName;
				tempPost = curr;
			}
		}
		Event *last = thread->at(0);
		if (tempPost->preEventName == last->preEventName) {
			last->postEventName = postEventName;
		} else {
			last->postEventName = tempPost->postEventName;
			postEventName = last->eventName;
		}
//		for (unsigned i = 0; i < thread->size(); i++) {
//			std::cerr << "eventName = " << thread->at(i)->eventName <<
//				", postEventName = " << thread->at(i)->postEventName << std::endl;
//		}
	}
}

//level: 0--bitcode; 1--source code; 2--block
void Encode::controlGranularity(int level) {
//	map<string, InstType> record;
	if (level == 0)
		return;
	else if (level == 1) {
		for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
			std::vector<Event*>* thread = trace->eventList[tid];
			if (thread == NULL)
				continue;
			Event* pre = thread->at(0);
			int preLineNum = pre->inst->info->line;
			InstType preInstType = getInstOpType(thread->at(0));
			string preEventName = thread->at(0)->eventName;

			for (unsigned index = 1, size = thread->size(); index < size;
					index++) {
				Event* curr = thread->at(index);
				InstType currInstType = getInstOpType(curr);

				//debug
//				curr->inst->inst->print(cerr);
//				if (currInstType == NormalOp)
//					cerr << "\noptype : NormalOp\n";
//				else if (currInstType == GlobalVarOp)
//					cerr << "\noptype : GlobalVarOp\n";
//				else if (currInstType == ThreadOp)
//					cerr << "\noptype : ThreadOp\n";
//				else
//					assert(0);

				int currLineNum = thread->at(index)->inst->info->line;

				if (currLineNum == preLineNum) {
					if (preInstType == NormalOp) {
						curr->eventName = preEventName;
						preInstType = currInstType;
					} else {
						if (currInstType == NormalOp) {
							curr->eventName = preEventName;
						} else {
							preInstType = currInstType;
							preEventName = curr->eventName;
						}
					}
				} else {
					preLineNum = currLineNum;
					preInstType = currInstType;
					preEventName = curr->eventName;
				}
			}
		}
	} else if (level == 2) {
		for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
			std::vector<Event*>* thread = trace->eventList[tid];
			if (thread == NULL)
				continue;
			Event* pre = thread->at(0);
			InstType preInstType = getInstOpType(pre);
			string preEventName = pre->eventName;

			for (unsigned index = 1, size = thread->size(); index < size;
					index++) {
				Event* curr = thread->at(index);
				InstType currInstType = getInstOpType(curr);

				//debug
//				curr->inst->inst->print(cerr);
//				cerr << "\n";
//				if (currInstType == NormalOp)
//					cerr << "NormalOp!\n";
//				else if (currInstType == GlobalVarOp)
//					cerr << "GlobalVarOp!\n";
//				else if (currInstType == ThreadOp)
//					cerr << "ThreadOp!\n";

				if (preInstType == NormalOp) {
					curr->eventName = preEventName;
				} else {
					preEventName = curr->eventName;
				}
				preInstType = currInstType;
			}
		}
	} else {
		//new level added by PeiLIU, aggregate by globalVar's load and store instruction.
		//level 3 is wrong, cannot use.
		std::cerr << "level 3\n";
		for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
			std::vector<Event*>* thread = trace->eventList[tid];
			if (thread == NULL)
				continue;
			Event* pre = thread->at(0);
			InstType preInstType = getInstOpType(pre);
			string preEventName = pre->eventName;


			unsigned index = 1, size = thread->size();
			while (index < size) {
				Event* curr = thread->at(index);
				InstType currInstType = getInstOpType(curr);
				if (currInstType == ThreadOp) {
					index++;
					if (index < size) {
						Event *temp = thread->at(index);
						preEventName = temp->eventName;
						preInstType = getInstOpType(temp);
					}
				} else {
					if (curr->isGlobal && ((curr->inst->inst->getOpcode() == Instruction::Load) ||
						(curr->inst->inst->getOpcode() == Instruction::Store))) {
						if (curr->inst->inst->getOpcode() == Instruction::Load) {
							Type::TypeID id = curr->inst->inst->getType()->getTypeID();
							if (((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) ||
									id == Type::IntegerTyID) {
								preEventName = curr->eventName;
							} else {
								curr->eventName = preEventName;
							}
						}
						if (curr->inst->inst->getOpcode() == Instruction::Store) {
							Type::TypeID id = curr->inst->inst->getOperand(0)->getType()->getTypeID();
							if (((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) ||
									id == Type::IntegerTyID) {
								preEventName = curr->eventName;
							} else {
								curr->eventName = preEventName;
							}
						}
					} else {
						curr->eventName = preEventName;
					}
				}
				preInstType = currInstType;
				index++;
				/*
				if (curr->isGlobal) {
					preEventName = curr->eventName;

					if (curr->inst->inst->getOpcode() == Instruction::Load) {
						bool isFloat = 0;
						Type::TypeID id = curr->inst->inst->getType()->getTypeID();
						if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
							isFloat = 1;
						}
						if (isFloat || id == Type::IntegerTyID) {
							preEventName = curr->eventName;
						} else {
							curr->eventName = preEventName;
						}
					} else if (curr->inst->inst->getOpcode() == Instruction::Store) {
						bool isFloat = 0;
						Type::TypeID id = curr->inst->inst->getOperand(0)->getType()->getTypeID();
						if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
							isFloat = 1;
						}
						if (isFloat || id == Type::IntegerTyID) {
							preEventName = curr->eventName;
						} else {
							curr->eventName = preEventName;
						}
					} else {
						curr->eventName = preEventName;
					}

				} else {
					curr->eventName = preEventName;
				}
				*/
			}
		}
	}
}

InstType Encode::getInstOpType(Event * event) {
	if (event->isGlobal) {
		return GlobalVarOp;
	}
	Instruction *I = event->inst->inst;
//	if (BranchInst::classof(I)) {
//		BranchInst* brI = dyn_cast<BranchInst>(I);
//		if (brI->isConditional()) {
//			return GlobalVarOp; //actually it's a br. just using
//		}
//	}
	if (!CallInst::classof(I)) {
		return NormalOp;
	}
//switch
//	CallInst* callI = dyn_cast<CallInst>(I);
//	if (callI->getCalledFunction() == NULL)
	if (event->calledFunction == NULL) {
		return NormalOp;
	}
//switch
//	const char* functionName = callI->getCalledFunction()->getName().data();
	const char* functionName = event->calledFunction->getName().data();

	if (strncmp("pthread", functionName, 7) == 0) {
		return ThreadOp;
	}
	return NormalOp;
}

void Encode::buildPartialOrderFormula() {
#if FORMULA_DEBUG
	cerr << "\nPartialOrderFormula:\n";
#endif
//handle thread_create
	std::map<Event*, uint64_t>::iterator itc = trace->createThreadPoint.begin();
	for (; itc != trace->createThreadPoint.end(); itc++) {
		//the event is at the point of creating thread
		string creatPoint = itc->first->eventName;
		//the event is the first step of created thread
		string firstStep = trace->eventList[itc->second]->at(0)->eventName;
		expr prev = z3_ctx.int_const(creatPoint.c_str());
		expr back = z3_ctx.int_const(firstStep.c_str());
		expr twoEventOrder = (prev < back);
#if FORMULA_DEBUG
		cerr << twoEventOrder << "\n";
#endif
		z3_solver.add(twoEventOrder);
	}
	//statics
	formulaNum += trace->createThreadPoint.size();

//handle thread_join
	std::map<Event*, uint64_t>::iterator itj = trace->joinThreadPoint.begin();
	for (; itj != trace->joinThreadPoint.end(); itj++) {
		//the event is at the point of joining thread
		string joinPoint = itj->first->eventName;
		//the event is the last step of joined thread
		string lastStep = trace->eventList[itj->second]->back()->eventName;
		expr prev = z3_ctx.int_const(lastStep.c_str());
		expr back = z3_ctx.int_const(joinPoint.c_str());
		expr twoEventOrder = (prev < back);
#if FORMULA_DEBUG
		cerr << twoEventOrder << "\n";
#endif
		z3_solver.add(twoEventOrder);
	}
	//statics
	formulaNum += trace->joinThreadPoint.size();
}

void Encode::buildReadWriteFormula() {
#if FORMULA_DEBUG
	cerr << "\nReadWriteFormula:\n";
#endif
//prepare
	//get read write set from copy one
//	trace->readSet.clear();
//	trace->writeSet.clear();
//	trace->readSet.insert(trace->copyReadSet.begin(), trace->copyReadSet.end());
//	trace->writeSet.insert(trace->copyWriteSet.begin(), trace->copyWriteSet.end());
	markLatestWriteForGlobalVar();
//
//	cerr << "size : " << trace->readSet.size()<<"\n";
//	cerr << "size : " << trace->writeSet.size()<<"\n";
	map<string, vector<Event *> >::iterator read;
	map<string, vector<Event *> >::iterator write;

//debug
//print out all the read and write insts of global vars.
	if (false) {
		read = trace->readSet.begin();
		for (; read != trace->readSet.end(); read++) {
			cerr << "global var read:" << read->first << "\n";
			for (unsigned i = 0; i < read->second.size(); i++) {
				cerr << read->second[i]->eventName << "---"
						<< read->second[i]->globalVarFullName << "\n";
			}
		}
		write = trace->writeSet.begin();
		for (; write != trace->writeSet.end(); write++) {
			cerr << "global var write:" << write->first << "\n";
			for (unsigned i = 0; i < write->second.size(); i++) {
				cerr << write->second[i]->eventName << "---"
						<< write->second[i]->globalVarFullName << "\n";
			}
		}
	}
//debug

	map<string, vector<Event *> >::iterator ir = trace->readSet.begin(); //key--variable,
	Event *currentRead;
	Event *currentWrite;
	for (; ir != trace->readSet.end(); ir++) {
		map<string, vector<Event *> >::iterator iw = trace->writeSet.find(
				ir->first);
		//maybe use the initial value from Initialization.@2014.4.16
		//if(iw == writeSet.end())
		//continue;
		for (unsigned k = 0; k < ir->second.size(); k++) {
			vector<expr> oneVarAllRead;
			currentRead = ir->second[k];
			expr r = z3_ctx.int_const(currentRead->eventName.c_str());

			//compute the write set that may be used by currentRead;
			vector<Event *> mayBeRead;
			unsigned currentWriteThreadId;
			if (iw != trace->writeSet.end()) {
				for (unsigned i = 0; i < iw->second.size(); i++) {
					if (iw->second[i]->threadId == currentRead->threadId)
						continue;
					else
						mayBeRead.push_back(iw->second[i]);
				}
			}
			if (currentRead->latestWrite != NULL) {
				mayBeRead.push_back(currentRead->latestWrite);
			} else//if this read don't have the corresponding write, it may use from Initialization operation.
			{
				//so, build the formula constrainting this read uses from Initialization operation

				vector<expr> oneVarOneRead;
				expr equal = z3_ctx.bool_val(1);
				bool flag = readFromInitFormula(currentRead, equal);
				if (flag != false) {
					//statics
					formulaNum++;
					oneVarOneRead.push_back(equal);
					for (unsigned j = 0; j < mayBeRead.size(); j++) {
						currentWrite = mayBeRead[j];
						expr w = z3_ctx.int_const(
								currentWrite->eventName.c_str());
						expr order = r < w;
						oneVarOneRead.push_back(order);
					}
					//statics
					formulaNum += mayBeRead.size();
					expr readFromInit = makeExprsAnd(oneVarOneRead);
					oneVarAllRead.push_back(readFromInit);
				}
			}
			//

			for (unsigned i = 0; i < mayBeRead.size(); i++) {
				//cause the write operation of every thread is arranged in the executing order
				currentWrite = mayBeRead[i];
				currentWriteThreadId = currentWrite->threadId;
				vector<expr> oneVarOneRead;
				expr equal = readFromWriteFormula(currentRead, currentWrite,
						ir->first);
				oneVarOneRead.push_back(equal);

				expr w = z3_ctx.int_const(currentWrite->eventName.c_str());
				expr rw = (w < r);
				//statics
				formulaNum += 2;
				//-----optimization-----//
				//the next write in the same thread must be behind this read.
				if (i + 1 <= mayBeRead.size() - 1 &&			//short-circuit
						mayBeRead[i + 1]->threadId == currentWriteThreadId) {
					expr nextw = z3_ctx.int_const(
							mayBeRead[i + 1]->eventName.c_str());
					//statics
					formulaNum++;
					rw = (rw && (r < nextw));
				}
				//

				oneVarOneRead.push_back(rw);

				unsigned current = i;
				for (unsigned j = 0; j < mayBeRead.size(); j++) {
					if (current == j
							|| currentWriteThreadId == mayBeRead[j]->threadId)
						continue;
					expr temp = enumerateOrder(currentRead, currentWrite,
							mayBeRead[j]);
					//statics
					formulaNum += 2;
					oneVarOneRead.push_back(temp);
				}
				//equal if-and-only-if possibleOrder
				expr if_and_only_if = makeExprsAnd(oneVarOneRead);
				oneVarAllRead.push_back(if_and_only_if);
			}

			expr oneReadExprs = makeExprsOr(oneVarAllRead);
#if FORMULA_DEBUG
			cerr << oneReadExprs << "\n";
#endif
			z3_solver.add(oneReadExprs);
		}
	}
}

expr Encode::readFromWriteFormula(Event * read, Event * write, string var) {
	Instruction *I = read->inst->inst;
	const Type * type = I->getType();
	while (type->getTypeID() == Type::PointerTyID) {
		type = type->getPointerElementType();
	}
//assert(I->getType()->getTypeID() == Type::PointerTyID && "Wrong Type!");
	const z3::sort varType(llvmTy_to_z3Ty(type));
	expr r = z3_ctx.constant(read->globalVarFullName.c_str(), varType);
	string writeVarName = "";
	if (write->globalVarFullName == "" && !write->implicitGlobalVar.empty()) {
		for (unsigned i = 0; i < write->implicitGlobalVar.size(); i++) {
			if (strncmp(var.c_str(), write->implicitGlobalVar[i].c_str(),
					var.size()) == 0) {
#if FORMULA_DEBUG
				cerr << "Event name : " << write->eventName << "\n";
				cerr<< "rw : " << var.c_str() << "---"
//						<< it->first.c_str()
						<< "\n";
#endif
				writeVarName = write->implicitGlobalVar[i];
				break;
			}

		}
	} else
		writeVarName = write->globalVarFullName;

	expr w = z3_ctx.constant(writeVarName.c_str(), varType);
	return r == w;
}
/**
 * build the formula representing equality to initial value
 */
bool Encode::readFromInitFormula(Event * read, expr& ret) {
	Instruction *I = read->inst->inst;
	const Type * type = I->getType();
	while (type->getTypeID() == Type::PointerTyID) {
		type = type->getPointerElementType();
	}
	const z3::sort varType(llvmTy_to_z3Ty(type));
	expr r = z3_ctx.constant(read->globalVarFullName.c_str(), varType);
	string globalVar = read->varName;
	std::map<std::string, llvm::Constant*>::iterator tempIt =
			trace->global_variable_initializer.find(globalVar);
//	assert(
//			(tempIt != data.global_variable_initializer.end())
//					&& "Wrong with global var!");
//	cerr << "current event: " << read->eventName << "  current globalVar: " << globalVar << "\n";
	if (tempIt == trace->global_variable_initializer.end())
		return false;
	string str = tempIt->first + "_Init";
	expr w = z3_ctx.constant(str.c_str(), varType);
	ret = r == w;
	return true;
}

expr Encode::enumerateOrder(Event * read, Event * write, Event * anotherWrite) {
	expr prev = z3_ctx.int_const(write->eventName.c_str());
	expr back = z3_ctx.int_const(read->eventName.c_str());
	expr another = z3_ctx.int_const(anotherWrite->eventName.c_str());
	expr o = another < prev || another > back;
	return o;
}

void Encode::buildSynchronizeFormula() {
#if FORMULA_DEBUG
	cerr << "\nSynchronizeFormula:\n";
	cerr << "The sum of locks:" << trace->all_lock_unlock.size() << "\n";
#endif

//lock/unlock
	map<string, vector<LockPair *> >::iterator it =
			trace->all_lock_unlock.begin();
	for (; it != trace->all_lock_unlock.end(); it++) {
		vector<LockPair*> tempVec = it->second;
		int size = tempVec.size();
		/////////////////////debug/////////////////////////////
		//print out all the read and write insts of global vars.
		if (false) {
			cerr << it->first << "\n";
			for (int k = 0; k < size; k++) {
				cerr << "#lock#: " << tempVec[k]->lockEvent->eventName;
				cerr << "  #unlock#: " << tempVec[k]->unlockEvent->eventName
						<< "\n";
			}
		}
		/////////////////////debug/////////////////////////////
		for (int i = 0; i < size - 1; i++) {
			expr oneLock = z3_ctx.int_const(
					tempVec[i]->lockEvent->eventName.c_str());
			if (tempVec[i]->unlockEvent == NULL) {		//imcomplete lock pair
				continue;
			}
			expr oneUnlock = z3_ctx.int_const(
					tempVec[i]->unlockEvent->eventName.c_str());
			for (int j = i + 1; j < size; j++) {
				if (tempVec[i]->threadId == tempVec[j]->threadId)
					continue;

				expr twoLock = z3_ctx.int_const(
						tempVec[j]->lockEvent->eventName.c_str());
				expr twinLockPairOrder = z3_ctx.bool_val(1);
				if (tempVec[j]->unlockEvent == NULL) {	//imcomplete lock pair
					twinLockPairOrder = oneUnlock < twoLock;
					//statics
					formulaNum++;
				} else {
					expr twoUnlock = z3_ctx.int_const(
							tempVec[j]->unlockEvent->eventName.c_str());
					twinLockPairOrder = (oneUnlock < twoLock)
							|| (twoUnlock < oneLock);
					//statics
					formulaNum += 2;
				}
				z3_solver.add(twinLockPairOrder);
#if FORMULA_DEBUG
				cerr << twinLockPairOrder << "\n";
#endif
			}
		}
	}

//new method
//wait/signal
#if FORMULA_DEBUG
	cerr << "The sum of wait:" << trace->all_wait.size() << "\n";
	cerr << "The sum of signal:" << trace->all_signal.size() << "\n";
#endif
	map<string, vector<Wait_Lock *> >::iterator it_wait =
			trace->all_wait.begin();
	map<string, vector<Event *> >::iterator it_signal;

	for (; it_wait != trace->all_wait.end(); it_wait++) {
		it_signal = trace->all_signal.find(it_wait->first);
		if (it_signal == trace->all_signal.end())
			assert(0 && "Something wrong with wait/signal data collection!");
		vector<Wait_Lock *> waitSet = it_wait->second;
		string currCond = it_wait->first;
		for (unsigned i = 0; i < waitSet.size(); i++) {
			vector<expr> possibleMap;
			vector<expr> possibleValue;
			expr wait = z3_ctx.int_const(waitSet[i]->wait->eventName.c_str());
			expr lock_wait = z3_ctx.int_const(
					waitSet[i]->lock_by_wait->eventName.c_str());
			vector<Event *> signalSet = it_signal->second;
			for (unsigned j = 0; j < signalSet.size(); j++) {
				if (waitSet[i]->wait->threadId == signalSet[j]->threadId)
					continue;
				expr signal = z3_ctx.int_const(signalSet[j]->eventName.c_str());
				//Event_wait < Event_signal < lock_wait
				expr exprs_0 = wait < signal && signal < lock_wait;

				//m_w_s = 1
				stringstream ss;
				ss << currCond << "_" << waitSet[i]->wait->eventName << "_"
						<< signalSet[j]->eventName;
				expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
				expr exprs_1 = (map_wait_signal == 1);
				//range: p_w_s = 0 or p_w_s = 1
				expr exprs_2 = map_wait_signal >= 0 && map_wait_signal <= 1;

				possibleMap.push_back(exprs_0 && exprs_1);
				possibleValue.push_back(exprs_2);
				//statics
				formulaNum += 3;
			}
			expr one_wait = makeExprsOr(possibleMap);
			expr wait_value = makeExprsAnd(possibleValue);
#if FORMULA_DEBUG
			cerr << one_wait << "\n";
#endif
			z3_solver.add(one_wait);
			z3_solver.add(wait_value);
		}
	}

	//Sigma m_w_s <= 1
	it_signal = trace->all_signal.begin();
	for (; it_signal != trace->all_signal.end(); it_signal++) {
		it_wait = trace->all_wait.find(it_signal->first);
		if (it_wait == trace->all_wait.end())
			continue;
		vector<Event *> signalSet = it_signal->second;
		string currCond = it_signal->first;
		for (unsigned i = 0; i < signalSet.size(); i++) {
			vector<Wait_Lock *> waitSet = it_wait->second;
			string currSignalName = signalSet[i]->eventName;
			vector<expr> mapLabel;
			for (unsigned j = 0; j < waitSet.size(); j++) {
				stringstream ss;
				ss << currCond << "_" << waitSet[j]->wait->eventName << "_"
						<< currSignalName;
				expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
				mapLabel.push_back(map_wait_signal);
			}
			expr sum = makeExprsSum(mapLabel);
			expr relation = (sum <= 1);
			z3_solver.add(relation);
		}
	}

	//Sigma m_s_w >= 1
	it_wait = trace->all_wait.begin();
	for (; it_wait != trace->all_wait.end(); it_wait++) {
		it_signal = trace->all_signal.find(it_wait->first);
		if (it_signal == trace->all_signal.end())
			continue;
		vector<Wait_Lock *> waitSet = it_wait->second;
		string currCond = it_wait->first;
		for (unsigned i = 0; i < waitSet.size(); i++) {
			vector<Event *> signalSet = it_signal->second;
			string currWaitName = waitSet[i]->wait->eventName;
			vector<expr> mapLabel;
			for (unsigned j = 0; j < signalSet.size(); j++) {
				stringstream ss;
				ss << currCond << "_" << currWaitName << "_"
						<< signalSet[j]->eventName;
				expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
				mapLabel.push_back(map_wait_signal);
			}
			expr sum = makeExprsSum(mapLabel);
			expr relation = (sum >= 1);
			z3_solver.add(relation);
		}
	}

	//wipe off the w/s matching in the same thread
	it_wait = trace->all_wait.begin();
	for (; it_wait != trace->all_wait.end(); it_wait++) {
		it_signal = trace->all_signal.find(it_wait->first);
		if (it_signal == trace->all_signal.end())
			continue;
		vector<Wait_Lock *> waitSet = it_wait->second;
		string currCond = it_wait->first;
		for (unsigned i = 0; i < waitSet.size(); i++) {
			vector<Event *> signalSet = it_signal->second;
			string currWaitName = waitSet[i]->wait->eventName;
			unsigned currThreadId = waitSet[i]->wait->threadId;
			for (unsigned j = 0; j < signalSet.size(); j++) {
				if (currThreadId == signalSet[j]->threadId) {
					stringstream ss;
					ss << currCond << "_" << currWaitName << "_"
							<< signalSet[j]->eventName;
					expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
					z3_solver.add(map_wait_signal == 0);
				}
			}
		}
	}

//barrier
#if FORMULA_DEBUG
	cerr << "The sum of barrier:" << trace->all_barrier.size() << "\n";
#endif
	map<string, vector<Event *> >::iterator it_barrier =
			trace->all_barrier.begin();
	for (; it_barrier != trace->all_barrier.end(); it_barrier++) {
		vector<Event *> temp = it_barrier->second;
		for (unsigned i = 0; i < temp.size() - 1; i++) {
			if (temp[i]->threadId == temp[i + 1]->threadId)
				assert(0 && "Two barrier event can't be in a same thread!");
			expr exp1 = z3_ctx.int_const(temp[i]->eventName.c_str());
			expr exp2 = z3_ctx.int_const(temp[i + 1]->eventName.c_str());
			expr relation = (exp1 == exp2);

#if FORMULA_DEBUG
			cerr << relation << "\n";
#endif
			z3_solver.add(relation);
		}
	}
}

expr Encode::makeExprsAnd(vector<expr> exprs) {
	unsigned size = exprs.size();
	if (size == 0)
		return z3_ctx.bool_val(1);
	if (size == 1)
		return exprs[0];
	expr ret = exprs[0];
	for (unsigned i = 1; i < size; i++)
		ret = ret && exprs[i];
	ret.simplify();
	return ret;
}

expr Encode::makeExprsOr(vector<expr> exprs) {
	unsigned size = exprs.size();
	if (size == 0)
		return z3_ctx.bool_val(1);
	if (size == 1)
		return exprs[0];
	expr ret = exprs[0];
	for (unsigned i = 1; i < size; i++)
		ret = ret || exprs[i];
	ret.simplify();
	return ret;
}

expr Encode::makeExprsSum(vector<expr> exprs) {
	unsigned size = exprs.size();
	if (size == 0)
		assert(0 && "Wrong!");
	if (size == 1)
		return exprs[0];
	expr ret = exprs[0];
	for (unsigned i = 1; i < size; i++)
		ret = ret + exprs[i];
	ret.simplify();
	return ret;
}

}

