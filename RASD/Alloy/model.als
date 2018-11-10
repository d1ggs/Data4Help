open util/integer
open util/boolean

abstract sig Data {
  userID: Int,
  timestamp: Int
} { timestamp >= 0 }

sig GroupData {
  data: set Data
}

-- Int used for simplicity, instead of float
sig HealthStatus extends Data {
  bloodPressure: Int,
  heartRate: Int,
  GSR: Int
} { GSR > 0 and heartRate > 0 and bloodPressure > 0 }

-- Int used for simplicity, instead of float
sig Location extends Data {
  coordX: Int,
  coordY: Int
}

abstract sig Gender {}
one sig Male extends Gender {}
one sig Female extends Gender {}

-- IDnumber: Int used for simplicity, instead of String
sig User {
  IDnumber: Int,
  age: Int,
  gender: Gender
} { age > 0 }

-- timestamp = 0 used to assign a constant value to thresholds
sig Elderly extends User {
  threshold: HealthStatus
}{ age > 5 and threshold.timestamp = 0 }

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

-- two health status data related to the same user can't have the same timestamp
-- the same holds for location data
fact DataAreUniqueInTime {
  no disj loc1, loc2: Location | loc1.userID = loc2.userID and loc1.timestamp = loc2.timestamp
  and
  no disj hStatus1, hStatus2: HealthStatus |
    hStatus1.userID = hStatus2.userID and hStatus1.timestamp = hStatus2.timestamp
}

fact ThirdPartyGroupDataConnection {
  all groupR: GroupedDataReq | (some tp: ThirdParty | groupR.thirdPartyID = tp.ID)
}

fact IndividualPermissionsBelongToRequestHandler {
  all permission: IndividualReqPermission |
    (some rHandler: RequestHandler | permission in rHandler.singlePermissions)
}

fact IndividualPermissionsThirdPartyUserConnection {
  all permission: IndividualReqPermission |
    (some u: User, tp: ThirdParty | permission.userID = u.IDnumber and permission.thirdPartyID = tp.ID)
}

fact GroupDataRequestsBelongToRequestHandler {
  all groupR: GroupedDataReq |
    (some rHandler: RequestHandler | groupR in rHandler.groupDataSubscriptions)
}

fact thirdPartyCanAccessOnlyToGrantedData {
  all tp: ThirdParty | (
    all data: tp.userData | (
      some r: IndividualReqPermission | r.userID = data.userID and r.thirdPartyID = tp.ID
    )
  )
}

fact ElderlyAmbulanceConnection {
  all amb: ExtAmbulanceProvider | (
    all old: amb.peopleToRescue | (
      some hStatus: HealthStatus | hStatus.userID = old.IDnumber and
                                                 hStatus.bloodPressure > old.threshold.bloodPressure and
                                                 hStatus.GSR < old.threshold.GSR and
                                                 hStatus.heartRate > old.threshold.heartRate and
        (all hStatus2: HealthStatus | hStatus2 != hStatus implies hStatus2.timestamp < hStatus.timestamp)
    )
  )
}

pred showThirdPartyWithUserData {
  some tp: ThirdParty | #tp.userData > 0 and
  some rHandler: RequestHandler | #rHandler.singlePermissions > 0
  and no Run and no Organizer and no Athlete and no Elderly
  and one User and one ThirdParty
}

pred showAutomatedSOS {
  some ambulance: ExtAmbulanceProvider | #ambulance.peopleToRescue > 0
  and no Organizer and no Athlete and no Run
  and no ThirdParty and no GroupData
  and one User
}

run showThirdPartyWithUserData for 3 but 1 GroupData, 1 GroupedDataReq, 1 IndividualReqPermission
-- run showAutomatedSOS for 3
