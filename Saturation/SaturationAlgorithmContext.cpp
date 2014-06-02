/**
 * @file SaturationAlgorithmContext.cpp
 *
 * @date 2 Jun 2014
 * @author dmitry
 */

#include "Kernel/MainLoopContext.hpp"
#include "Kernel/Problem.hpp"
#include "Lib/Timer.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Options.hpp"

#include "SaturationAlgorithmContext.hpp"

using Kernel::MainLoopContext;
using Kernel::Problem;
using Lib::Timer;
using Shell::Options;

namespace Saturation {

SaturationAlgorithmContext::SaturationAlgorithmContext(Problem& prb, Options& opts):
		MainLoopContext(prb, opts) {
	CALL("SaturationAlgorithmContext::SaturationAlgorithmContext(Problem& prb, Options& opts)");

	switchIn();

	_ml = SaturationAlgorithm::createFromOptions(_prb, _opt);

	switchOut();
}

SaturationAlgorithmContext::~SaturationAlgorithmContext() {
	CALL("SaturationAlgorithmContext::~SaturationAlgorithmContext()");

	delete _ml;
}

void SaturationAlgorithmContext::init(){
	CALL("SaturationAlgorithmContext::init");

	switchIn();

	_env -> statistics -> phase = Statistics::SATURATION;
	_ml -> initAlgorithmRun();

	switchOut();
}

void SaturationAlgorithmContext::cleanup(){
	CALL("SaturationAlgorithmContext::cleanup");

	switchIn();

	_env -> statistics -> phase = Statistics::FINALIZATION;

	switchOut();
}

void SaturationAlgorithmContext::doStep() {
	CALL("SaturationAlgorithmContext::doStep()");

	switchIn();
	_ml -> doOneAlgorithmStep();

	Timer::syncClock();
	if (env -> timeLimitReached()) {
		throw  TimeLimitExceededException();
	}

	switchOut();
}

};
