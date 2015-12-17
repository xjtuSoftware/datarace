//by hy 2015.7.21
//#include "klee/Internal/Module/KInstruction.h"
#include "DealWithSymbolicExpr.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Function.h"
//#include "llvm/IR/Instructions.h"
#include <sstream>
#include <ostream>
#include <set>
#include <stack>
#include <vector>
#include <map>

#define MAKECONCRETE 1

namespace klee {

//这里的是否使用一个map有待考虑.
std::set<std::string> relatedSymbolicExpr;
std::set<std::string> relatedVarName;

std::string DealWithSymbolicExpr::getVarName(ref<klee::Expr> value) {
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

std::string DealWithSymbolicExpr::getFullName(ref<klee::Expr> value) {

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

void DealWithSymbolicExpr::resolveSymbolicExpr(ref<klee::Expr> value,
		std::set<std::string>* relatedSymbolicExpr) {
	if (value->getKind() == Expr::Read) {
		std::string varName = getVarName(value);
		if (relatedSymbolicExpr->find(varName) == relatedSymbolicExpr->end()) {
			relatedSymbolicExpr->insert(varName);
		}
		return;
	} else {
		unsigned kidsNum = value->getNumKids();
		if (kidsNum == 2 && value->getKid(0) == value->getKid(1)) {
			resolveSymbolicExpr(value->getKid(0), relatedSymbolicExpr);
		} else {
			for (unsigned int i = 0; i < kidsNum; i++) {
				resolveSymbolicExpr(value->getKid(i), relatedSymbolicExpr);
			}
		}
	}
}

void DealWithSymbolicExpr::resolveSymbolicExpr(ref<klee::Expr> value) {
	if (value->getKind() == Expr::Read) {
		std::string varName = getVarName(value);
		if (relatedSymbolicExpr.find(varName) == relatedSymbolicExpr.end()) {
			relatedSymbolicExpr.insert(varName);
		}
		return;
	} else {
		unsigned kidsNum = value->getNumKids();
		if (kidsNum == 2 && value->getKid(0) == value->getKid(1)) {
			resolveSymbolicExpr(value->getKid(0));
		} else {
			for (unsigned int i = 0; i < kidsNum; i++) {
				resolveSymbolicExpr(value->getKid(i));
			}
		}
	}
}

void DealWithSymbolicExpr::addExprToSet(std::set<std::string>* Expr,
		std::set<std::string>* relatedSymbolicExpr) {

	for (std::set<std::string>::iterator it =
			Expr->begin(), ie = Expr->end(); it != ie; ++it) {
		std::string varName =*it;
		if (relatedSymbolicExpr->find(varName) == relatedSymbolicExpr->end()) {
			relatedSymbolicExpr->insert(varName);
		}
	}
}

#if !MAKECONCRETE
void DealWithSymbolicExpr::filterUseless(Trace* trace) {

	//get the copy readSet and writeSet
	trace->copyReadSet.insert(trace->readSet.begin(), trace->readSet.end());
	trace->copyWriteSet.insert(trace->writeSet.begin(), trace->writeSet.end());
	trace->copy_global_variable_initializer.insert(trace->global_variable_initializer.begin(),
			trace->global_variable_initializer.end());


	std::vector<std::string> remainingExprVarName;
	std::vector<ref<klee::Expr> > remainingExpr;
	allRelatedSymbolicExpr.clear();

	std::vector<ref<klee::Expr> > &storeSymbolicExpr = trace->storeSymbolicExpr;
	std::vector<ref<klee::Expr> > &brSymbolicExpr = trace->brSymbolicExpr;
	std::vector<ref<klee::Expr> > &assertSymbolicExpr = trace->assertSymbolicExpr;
	std::vector<ref<klee::Expr> > &kQueryExpr = trace->kQueryExpr;

	std::string varName;
//	relatedSymbolicExpr.clear();
//	std::cerr << "store expr\n";
	for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(), ie =
			storeSymbolicExpr.end(); it != ie; ++it) {
//		it->get()->dump();
		varName = getVarName(it->get()->getKid(1));
		remainingExprVarName.push_back(varName);
		remainingExpr.push_back(it->get());
	}
	for (std::vector<ref<Expr> >::iterator it = brSymbolicExpr.begin(), ie =
			brSymbolicExpr.end(); it != ie; ++it) {
		resolveSymbolicExpr(it->get(), &allRelatedSymbolicExpr);
//		kQueryExpr.push_back(it->get());
	}
	for (std::vector<ref<Expr> >::iterator it = assertSymbolicExpr.begin(), ie =
			assertSymbolicExpr.end(); it != ie; ++it) {
		resolveSymbolicExpr(it->get(), &allRelatedSymbolicExpr);
//		kQueryExpr.push_back(it->get());
	}
	std::map<std::string, std::set<std::string>* > &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	for (std::set<std::string>::iterator nit = allRelatedSymbolicExpr.begin();
			nit != allRelatedSymbolicExpr.end(); ++nit) {
		varName = *nit;
		std::vector<ref<Expr> >::iterator itt = remainingExpr.begin();
		for (std::vector<std::string>::iterator it =
				remainingExprVarName.begin(), ie = remainingExprVarName.end();
				it != ie;) {
			if (varName == *it) {
				remainingExprVarName.erase(it);
				--ie;
				kQueryExpr.push_back(*itt);

				std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
				resolveSymbolicExpr(itt->get(), tempSymbolicExpr);
				if (varRelatedSymbolicExpr.find(varName) != varRelatedSymbolicExpr.end()) {
					addExprToSet(tempSymbolicExpr, varRelatedSymbolicExpr[varName]);
				} else {
					varRelatedSymbolicExpr[varName] = tempSymbolicExpr;
				}
				addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
#if DEBUG
				std::cerr << "\n" << varName << "\n varRelatedSymbolicExpr " << std::endl;
				std::cerr << *itt << "\n";
				for (std::set<std::string>::iterator it = tempSymbolicExpr->begin(),
						ie = tempSymbolicExpr->end(); it != ie; ++it) {
					std::cerr << *it << std::endl;
				}
#endif
				remainingExpr.erase(itt);
			} else {
				++it;
				++itt;
			}
		}
	}
#if !DEBUG
	std::cerr << "\n" << varName << "\n varRelatedSymbolicExpr " << std::endl;
	for (std::map<std::string, std::set<std::string>* >::iterator nit = varRelatedSymbolicExpr.begin();
			nit != varRelatedSymbolicExpr.end(); ++nit) {
		std::cerr << "name : " << (*nit).first << "\n";
		for (std::set<std::string>::iterator it = (*nit).second->begin(),
				ie = (*nit).second->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
	}
#endif
	std::map<std::string, std::vector<Event *> > usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulReadSet.insert(*nit);
		}
	}
	readSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulReadSet.begin(), nie = usefulReadSet.end(); nit != nie;
			++nit) {
		readSet.insert(*nit);
	}

	std::map<std::string, std::vector<Event *> > usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulWriteSet.insert(*nit);
		}
	}
	writeSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulWriteSet.begin(), nie = usefulWriteSet.end(); nit != nie;
			++nit) {
		writeSet.insert(*nit);
	}

	std::map<std::string, llvm::Constant*> usefulGlobal_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	usefulGlobal_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulGlobal_variable_initializer.insert(*nit);
		}
	}
	global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			usefulGlobal_variable_initializer.begin(), nie = usefulGlobal_variable_initializer.end(); nit != nie;
			++nit) {
		global_variable_initializer.insert(*nit);
	}

//	std::vector<std::vector<Event*>*> eventList = trace->eventList;
//	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
//			currentEvent != endEvent; currentEvent++) {
//		if ((*currentEvent)->isGlobal == true) {
//			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
//					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
//				if (relatedSymbolicExpr.find((*currentEvent)->varName) == relatedSymbolicExpr.end()) {
//					(*currentEvent)->isGlobal = false;
//				}
//			}
//		}
//	}
}
#endif


#if MAKECONCRETE
void DealWithSymbolicExpr::filterUseless(Trace* trace) {

	//get the copy readSet and writeSet
	trace->copyReadSet.insert(trace->readSet.begin(), trace->readSet.end());
	trace->copyWriteSet.insert(trace->writeSet.begin(), trace->writeSet.end());
	trace->copy_global_variable_initializer.insert(trace->global_variable_initializer.begin(),
			trace->global_variable_initializer.end());


	std::vector<std::string> remainingExprVarName;
	std::vector<ref<klee::Expr> > remainingExpr;

	std::vector<ref<klee::Expr> > &storeSymbolicExpr = trace->storeSymbolicExpr;
	std::vector<ref<klee::Expr> > &brSymbolicExpr = trace->brSymbolicExpr;
	std::vector<ref<klee::Expr> > &assertSymbolicExpr = trace->assertSymbolicExpr;
	std::vector<ref<klee::Expr> > &kQueryExpr = trace->kQueryExpr;

	std::string varName;
	relatedSymbolicExpr.clear();
//	std::cerr << "store expr\n";
	for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(), ie =
			storeSymbolicExpr.end(); it != ie; ++it) {
//		it->get()->dump();
		varName = getVarName(it->get()->getKid(1));
		remainingExprVarName.push_back(varName);
		remainingExpr.push_back(it->get());
	}
	for (std::vector<ref<Expr> >::iterator it = brSymbolicExpr.begin(), ie =
			brSymbolicExpr.end(); it != ie; ++it) {
		resolveSymbolicExpr(it->get());
//		kQueryExpr.push_back(it->get());
	}
	for (std::vector<ref<Expr> >::iterator it = assertSymbolicExpr.begin(), ie =
			assertSymbolicExpr.end(); it != ie; ++it) {
		resolveSymbolicExpr(it->get());
//		kQueryExpr.push_back(it->get());
	}
	for (std::set<std::string>::iterator nit = relatedSymbolicExpr.begin();
			nit != relatedSymbolicExpr.end(); ++nit) {
		varName = *nit;
		std::vector<ref<Expr> >::iterator itt = remainingExpr.begin();
		for (std::vector<std::string>::iterator it =
				remainingExprVarName.begin(), ie = remainingExprVarName.end();
				it != ie;) {
			if (varName == *it) {
				remainingExprVarName.erase(it);
				--ie;
				kQueryExpr.push_back(*itt);
				resolveSymbolicExpr(itt->get());
				remainingExpr.erase(itt);
			} else {
				++it;
				++itt;
			}
		}
	}
	std::map<std::string, std::vector<Event *> > usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (relatedSymbolicExpr.find(varName) != relatedSymbolicExpr.end()) {
			usefulReadSet.insert(*nit);
		}
	}
	readSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulReadSet.begin(), nie = usefulReadSet.end(); nit != nie;
			++nit) {
		readSet.insert(*nit);
	}

	std::map<std::string, std::vector<Event *> > usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (relatedSymbolicExpr.find(varName) != relatedSymbolicExpr.end()) {
			usefulWriteSet.insert(*nit);
		}
	}
	writeSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulWriteSet.begin(), nie = usefulWriteSet.end(); nit != nie;
			++nit) {
		writeSet.insert(*nit);
	}

	std::map<std::string, llvm::Constant*> usefulGlobal_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	usefulGlobal_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (relatedSymbolicExpr.find(varName) != relatedSymbolicExpr.end()) {
			usefulGlobal_variable_initializer.insert(*nit);
		}
	}
	global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			usefulGlobal_variable_initializer.begin(), nie = usefulGlobal_variable_initializer.end(); nit != nie;
			++nit) {
		global_variable_initializer.insert(*nit);
	}

//	std::vector<std::vector<Event*>*> eventList = trace->eventList;
//	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
//			currentEvent != endEvent; currentEvent++) {
//		if ((*currentEvent)->isGlobal == true) {
//			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
//					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
//				if (relatedSymbolicExpr.find((*currentEvent)->varName) == relatedSymbolicExpr.end()) {
//					(*currentEvent)->isGlobal = false;
//				}
//			}
//		}
//	}
}
#endif


void DealWithSymbolicExpr::getGlobalVarAllRelated(Trace *trace, std::string varStr)
{
	trace->globalVarAllRelated.insert(varStr);
	std::map<std::string, std::set<std::string> >::iterator it =
			trace->globalVarFirstOrderRelated.find(varStr);
	if (it != trace->globalVarFirstOrderRelated.end()) {
		std::set<std::string> &temp = it->second;
		std::set<std::string>::iterator it = temp.begin(), ie = temp.end();
		for (; it != ie; it++) {
			if (trace->globalVarAllRelated.find(*it) != trace->globalVarAllRelated.end()) {
				getGlobalVarAllRelated(trace, *it);
			}
		}
	}
}


void DealWithSymbolicExpr::filterUselessWithSet(Trace* trace,
		std::set<std::string>* relatedSymbolicExpr){
	std::set<std::string> &RelatedSymbolicExpr = trace->RelatedSymbolicExpr;
	RelatedSymbolicExpr.clear();
#if DEBUG
	std::cerr << "\n relatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = relatedSymbolicExpr->begin(),
			ie = relatedSymbolicExpr->end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif
	addExprToSet(relatedSymbolicExpr, &RelatedSymbolicExpr);

	std::string varName;
	std::map<std::string, std::set<std::string>* > &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	for (std::set<std::string>::iterator nit = RelatedSymbolicExpr.begin();
			nit != RelatedSymbolicExpr.end(); ++nit) {
		varName = *nit;
#if DEBUG
		std::cerr << "\n varName : " <<  varName << std::endl;
#endif
		if (varRelatedSymbolicExpr.find(varName) != varRelatedSymbolicExpr.end()) {
			addExprToSet(varRelatedSymbolicExpr[varName], &RelatedSymbolicExpr);
		}
#if DEBUG
		std::cerr << "\n addExprToSet(relatedSymbolicExpr, &RelatedSymbolicExpr); " << std::endl;
#endif
	}
#if DEBUG
	std::cerr << "\n RelatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = RelatedSymbolicExpr.begin(),
			ie = RelatedSymbolicExpr.end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif
}



void DealWithSymbolicExpr::resolveGlobalVarName(ref<klee::Expr> value)
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


void DealWithSymbolicExpr::getGlobalFirstOrderRelated(Trace * trace)
{
//	std::cerr << "store expr\n";
	std::vector<ref<klee::Expr> > &storeSymbolicExpr = trace->storeSymbolicExpr;
	std::string varName = "";
	for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(), ie =
			storeSymbolicExpr.end(); it != ie; ++it) {
//		it->get()->dump();

		varName = getVarName(it->get()->getKid(1));
		trace->remainingExpr.push_back(*it);
		trace->remainingExprVarName.push_back(varName);
		relatedVarName.clear();
		resolveGlobalVarName(it->get()->getKid(0));
		if (relatedVarName.find(varName) != relatedVarName.end()) {
			relatedVarName.erase(varName);
		}
		if (trace->globalVarFirstOrderRelated.find(varName) ==
				trace->globalVarFirstOrderRelated.end()) {
			trace->globalVarFirstOrderRelated.insert(make_pair(varName, relatedVarName));
		} else {
			std::set<std::string> &temp = trace->globalVarFirstOrderRelated.find(varName)->second;
			temp.insert(relatedVarName.begin(), relatedVarName.end());
		}
	}
//	std::cerr << "trace->globalVarFirstOrderRelated = " << trace->globalVarFirstOrderRelated.size() << std::endl;
//	std::map<std::string, std::set<std::string> >::iterator git =
//			trace->globalVarFirstOrderRelated.begin(), gie = trace->globalVarFirstOrderRelated.end();
//	for (; git != gie; git++) {
//		std::cerr << "first : " << git->first << ", " << git->second.size() << std::endl;
//	}

}

void DealWithSymbolicExpr::getGlobalVarRelatedLock(Trace* trace)
{
	std::map<unsigned, std::vector<std::string> > threadMapLock;
	std::vector<std::vector<Event*>*>::iterator tit = trace->eventList.begin(),
			tie = trace->eventList.end();
	std::cerr << "eventList size = " << trace->eventList.size() << std::endl;
	for (;tit != tie; tit++) {
		std::vector<Event*>* thread = *tit;
		if (thread == NULL)
			continue;
//		std::cerr << "thread->size = " << thread->size() << std::endl;
		for (unsigned index = 0, size = thread->size(); index < size; index++) {
			Event *event = thread->at(index);
//			event->inst->inst->dump();
			unsigned threadId = event->threadId;
			if (event->inst->inst->getOpcode() == llvm::Instruction::Call) {
				llvm::Function * f = event->calledFunction;
//				std::cerr << "f->getName = " << f->getName().str() << std::endl;
				if (f->getName().str() == "pthread_mutex_lock") {
					if (threadMapLock.find(threadId) == threadMapLock.end()) {
						std::vector<std::string> lockVector;
						lockVector.push_back(event->mutexName);
						threadMapLock.insert(make_pair(threadId, lockVector));
					} else {
						threadMapLock.find(threadId)->second.push_back(event->mutexName);
					}
				}
				if (f->getName().str() == "pthread_mutex_unlock") {
					threadMapLock.find(threadId)->second.pop_back();
				}
			}
			if ((threadMapLock.find(threadId) != threadMapLock.end()) &&
					!threadMapLock.find(threadId)->second.empty() && event->isGlobal) {
//				std::cerr << "threadMapLock : " << threadMapLock.size() << std::endl;
				if (trace->globalVarRelatedLock.find(event->varName) ==
						trace->globalVarRelatedLock.end()) {
					std::set<std::string> lockSet;
					lockSet.insert(threadMapLock.find(threadId)->second.begin(),
							threadMapLock.find(threadId)->second.end());
					trace->globalVarRelatedLock.insert(make_pair(event->varName, lockSet));
				} else {
					trace->globalVarRelatedLock.find(event->varName)->second.insert(
							threadMapLock.find(threadId)->second.begin(), threadMapLock.find(threadId)->second.end());
				}
			}
		}
	}
//	std::cerr << "every global var protected by some locks:\n";
//	std::map<std::string, std::set<std::string> >::iterator it = trace->globalVarRelatedLock.begin(),
//			ie = trace->globalVarRelatedLock.end();
//	for (; it != ie; it++) {
//		std::cerr << "gloabl varName = " << it->first << ", and locks are: \n";
//		std::set<std::string>::iterator sit = it->second.begin(), sie = it->second.end();
//		for (; sit != sie; sit++) {
//			std::cerr << *sit << "  ";
//		}
//		std::cerr << std::endl;
//	}
}


/*
void DealWithSymbolicExpr::getUsefulGlobalVar(Trace * trace, std::string str)
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

void DealWithSymbolicExpr::getPathCondition(Trace *trace)
{
	std::vector<ref<klee::Expr> > &kQueryExpr = trace->kQueryExpr;
	for (std::set<std::string>::iterator it = trace->usefulGlobalVar.begin(),
			ie = trace->usefulGlobalVar.end(); it != ie; it++) {
		std::string varName = *it;
		std::vector<ref<Expr> >::iterator itt = trace->remainingExpr.begin();
		for (std::vector<std::string>::iterator rit = trace->remainingExprVarName.begin(),
				rie = trace->remainingExprVarName.end(); rit != rie; rit++, itt++) {
//			if (varName == *rit) {
				kQueryExpr.push_back(*itt);
//			}
		}
	}
}
void DealWithSymbolicExpr::getBaseUsefulExpr(Trace* trace, std::string str)
{
	getUsefulGlobalVar(trace, str);
	std::map<std::string, std::vector<Event *> > usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator it = readSet.begin(),
			ie = readSet.end(); it != ie; it++) {
		if (trace->usefulGlobalVar.find(it->first) != trace->usefulGlobalVar.end()) {
			usefulReadSet.insert(*it);
		}
	}
	readSet.clear();
	readSet.insert(usefulReadSet.begin(), usefulReadSet.end());
	std::map<std::string, std::vector<Event *> > usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator it = writeSet.begin(),
			ie = writeSet.end(); it != ie; it++) {
		if (trace->usefulGlobalVar.find(it->first) != trace->usefulGlobalVar.end()) {
			usefulWriteSet.insert(*it);
		}
	}
	writeSet.clear();
	writeSet.insert(usefulWriteSet.begin(), usefulWriteSet.end());

	std::map<std::string, llvm::Constant*> usefulGlobal_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	usefulGlobal_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		if (trace->usefulGlobalVar.find(nit->first) != trace->usefulGlobalVar.end()) {
			usefulGlobal_variable_initializer.insert(*nit);
		}
	}
	global_variable_initializer.clear();
	global_variable_initializer.insert(usefulGlobal_variable_initializer.begin(),
			usefulGlobal_variable_initializer.end());

	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
			currentEvent != endEvent; currentEvent++) {
		if ((*currentEvent)->isGlobal == true) {
			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
				if (trace->usefulGlobalVar.find((*currentEvent)->varName) == trace->usefulGlobalVar.end()) {
					(*currentEvent)->isGlobal = false;
				}
			}
		}
	}
}

void DealWithSymbolicExpr::getGlobalVarRelatedLock(Trace* trace)
{
	std::map<unsigned, std::vector<std::string> > threadMapLock;
	std::vector<std::vector<Event*>*>::iterator tit = trace->eventList.begin(),
			tie = trace->eventList.end();
	for (;tit != tie; tit++) {
		std::vector<Event*>* thread = *tit;
		if (thread == NULL)
			continue;
		for (unsigned index = 0, size = thread->size(); index < size; index++) {
			Event *event = thread->at(index);
			unsigned threadId = event->threadId;
			if (event->inst->inst->getOpcode() == llvm::Instruction::Call) {
				llvm::Function * f = event->calledFunction;
				if (f->getName().str() == "pthread_mutex_lock") {
					if (threadMapLock.find(threadId) == threadMapLock.end()) {
						std::vector<std::string> lockVector;
						lockVector.push_back(event->mutexName);
						threadMapLock.insert(make_pair(threadId, lockVector));
					} else {
						threadMapLock.find(threadId)->second.push_back(event->mutexName);
					}
				}
				if (f->getName().str() == "pthread_mutex_unlock") {
					threadMapLock.find(threadId)->second.pop_back();
				}
			}
			if (!threadMapLock.find(threadId)->second.empty() && event->isGlobal) {
				if (trace->globalVarRelatedLock.find(event->varName) ==
						trace->globalVarRelatedLock.end()) {
					std::set<std::string> lockSet;
					lockSet.insert(threadMapLock.find(threadId)->second.begin(),
							threadMapLock.find(threadId)->second.end());
					trace->globalVarRelatedLock.insert(make_pair(event->varName, lockSet));
				} else {
					trace->globalVarRelatedLock.find(event->varName)->second.insert(
							threadMapLock.find(threadId)->second.begin(), threadMapLock.find(threadId)->second.end());
				}
			}
		}
	}
}

void DealWithSymbolicExpr::getUsefulLockPair(Trace *trace)
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
	trace->all_lock_unlock.clear();
	trace->all_lock_unlock.insert(usefulLockPair.begin(), usefulLockPair.end());
}
*/

void DealWithSymbolicExpr::copyCollectedDataOfTrace(Trace *trace)
{
//	std::cerr << "these size : readSet " << trace->readSet.size() << " " <<
//			"writeSet : " << trace->writeSet.size() << " " <<
//			"all_lock_unlock : " << trace->all_lock_unlock.size() << " " <<
//			"global_variable_initializer : " << trace->global_variable_initializer.size() << " " <<
//			std::endl;
	trace->copyReadSet.clear();
	trace->copyWriteSet.clear();
	trace->copy_all_lock_unlock.clear();
	trace->copy_global_variable_initializer.clear();
//	for (std::map<std::string, std::vector<Event *> >::iterator it = trace->readSet.begin(),
//			ie = trace->readSet.end(); it != ie; it++) {
//		std::cerr << "why not?\n";
//		trace->copyReadSet.insert(*it);
//	}
	trace->copyReadSet.insert(trace->readSet.begin(), trace->readSet.end());
	trace->copyWriteSet.insert(trace->writeSet.begin(), trace->writeSet.end());
	trace->copy_all_lock_unlock.insert(trace->all_lock_unlock.begin(), trace->all_lock_unlock.end());
	trace->copy_global_variable_initializer.insert(trace->global_variable_initializer.begin(),
			trace->global_variable_initializer.end());
//	trace->copy_eventList(trace->copy_eventList.end(), trace->eventList.begin(), trace->eventList.end());

//	std::cerr << "these size : copyReadSet " << trace->copyReadSet.size() << " " <<
//			"copyWriteSet : " << trace->copyWriteSet.size() << " " <<
//			"copy_all_lock_unlock : " << trace->copy_all_lock_unlock.size() << " " <<
//			"global_variable_initializer : " << trace->copy_global_variable_initializer.size() << " " <<
//			std::endl;
}

}
