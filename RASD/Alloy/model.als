-- TODO: Model Int type
abstract sig Data {
	userID: Int,
	timestamp: Int
}

sig GroupData {
	(0 or more) Data
}

-- MODIFY CLASS DIAGRAM ACCORDINGLY
sig HealthStatus extends Data {
	bloodPressure: Double,
	heartRate: Int,
	GSR: Double
}

-- TODO: Model double type
sig Location extends Data {
	coordX: Double,
	coordY: Double
}

sig User {
	IDnumber: String,
	personalData
}

-- Don't know if it's possible to extend a non-abstract sig
-- USED FOR AUTOMATEDSOS TESTCASE
sig Elderly extends User { }

-- USED FOR TRACK4RUN TESTCASE
sig Athlete extends User { }

sig ThirdParty {
	ID: Int
}

-- USED FOR TRACK4RUN TESTCASE
sig Organizer extends ThirdParty { }

-- USED FOR DATA REQUESTS TESTCASES
one RequestHandler {
	(0 or more) IndividualReqPermission,
	(0 or more) GroupedDataReq
}

-- TODO: Model Bool type
sig IndividualReqPermission {
	userID: String,
	thirdPartyID: Int,
	allowed: Bool,
	pending: Bool
}

-- subscription with timed updates
sig GroupedDataReq {
	searchParameters,
	thirdPartyID: Int,
	updateInterval: Int
}

-- USED FOR AUTOMATEDSOS TESTCASE
one DataCollector { }

-- USED FOR AUTOMATEDSOS TESTCASE
one ParametersInspector { }

-- USED FOR TRACK4RUN TESTCASE
sig Run {
	startTime: Int,
	endTime: Int,
	track
}
