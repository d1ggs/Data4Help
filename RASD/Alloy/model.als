open util/integer
open util/boolean

abstract sig Data {
  userID: Int,
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
  IDnumber: Int,
  age: Int,
  gender: Gender,
  ownData: set Data
} { age > 0 }

-- USED FOR AUTOMATEDSOS TESTCASE
sig Elderly extends User {
  threshold: HealthStatus
}{ age > 60 }

-- USED FOR TRACK4RUN TESTCASE
sig Athlete extends User {}

sig ThirdParty {
  ID: Int,
  userData: set Data
}

one sig ExtAmbulanceProvider {
  peopleToRescue: set Elderly
}

-- USED FOR TRACK4RUN TESTCASE
sig Organizer extends ThirdParty {}

-- USED FOR DATA REQUESTS TESTCASES
one sig RequestHandler {
  singlePermissions: set IndividualReqPermission,
  groupDataSubscriptions: set GroupedDataReq
}

sig IndividualReqPermission {
  userID: Int,
  thirdPartyID: Int,
  allowed: Bool,
  pending: Bool
} { pending = True implies allowed = False }

-- subscription with timed updates
sig GroupedDataReq {
  --searchParameters, -- should we specify it?
  thirdPartyID: Int,
  --updateInterval: Int
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
 

fact usersAreUnique {
  no disj u1, u2: User | u1.IDnumber = u2.IDnumber
}

fact thirdPartiesAreUnique {
  no disj tp1, tp2: ThirdParty | tp1.ID = tp2.ID
}

fact UserDataConnection {
  all data: Data | (some u: User | data.userID = u.IDnumber)
}

fact UserPermissionsConnection {
  all permission: IndividualReqPermission | (some u: User | permission.userID = u.IDnumber)
}

fact ThirdPartyGroupDataConnection {
  all groupR: GroupedDataReq | (some tp: ThirdParty | groupR.thirdPartyID = tp.ID)
}

fact IndividualPermissionsBelongToRequestHandler {
  all permission: IndividualReqPermission | (some rHandler: RequestHandler | permission in rHandler.singlePermissions)
}

fact GroupDataRequestsBelongToRequestHandler {
  all groupR: GroupedDataReq | (some rHandler: RequestHandler | groupR in rHandler.groupDataSubscriptions)
}

fact thirdPartyCanAccessOnlyToGrantedData {
  all tp: ThirdParty | (
    all data: tp.userData | (
      some r: IndividualReqPermission | r.userID = data.userID and r.thirdPartyID = tp.ID
    )
  )
}


pred show {
  some tp: ThirdParty | #tp.userData > 0 and
  some rHandler: RequestHandler | #rHandler.singlePermissions > 0
}

run show for 3 but 0 Run, 0 Organizer
