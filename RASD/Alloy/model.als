-- MODIFY CLASS DIAGRAM ACCORDINGLY
open util/integer
open util/boolean

abstract sig Data {
  userID: String,
  timestamp: Int
}

sig GroupData {
  data: set Data
}

-- Int used for simplicity, instead of float
sig HealthStatus extends Data {
  bloodPressure: Int,
  heartRate: Int,
  GSR: Int
}

sig Location extends Data {
  coordX: Int,
  coordY: Int
}

abstract sig Gender {}
one sig Male extends Gender {}
one sig Female extends Gender {}

sig User {
  IDnumber: String,
  firstName: String,
  lastName: String,
  age: Int,
  gender: Gender
}

-- USED FOR AUTOMATEDSOS TESTCASE
sig Elderly extends User {}{ age > 60 }

-- USED FOR TRACK4RUN TESTCASE
sig Athlete extends User {}

sig ThirdParty {
  ID: Int
}

-- USED FOR TRACK4RUN TESTCASE
sig Organizer extends ThirdParty {}

-- USED FOR DATA REQUESTS TESTCASES
one sig RequestHandler {
  permissions: set IndividualReqPermission,
  groupDataSubscriptions: set GroupedDataReq
}

sig IndividualReqPermission {
  userID: String,
  thirdPartyID: Int,
  allowed: Bool,
  pending: Bool
}

-- subscription with timed updates
sig GroupedDataReq {
  searchParameters, -- should we specify it?
  thirdPartyID: Int,
  updateInterval: Int
}

-- USED FOR AUTOMATEDSOS TESTCASE
one sig DataCollector { }

-- USED FOR AUTOMATEDSOS TESTCASE
one sig ParametersInspector { }

-- USED FOR TRACK4RUN TESTCASE
sig Run {
  startTime: Int,
  endTime: Int,
  --track
}


