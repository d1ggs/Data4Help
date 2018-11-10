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

sig Athlete extends User {
  enrolledRuns: set Run
}

sig ThirdParty {
  ID: Int,
  userData: set Data,
  groupData: set GroupData
}

one sig ExtAmbulanceProvider {
  peopleToRescue: set Elderly
}

one sig RequestHandler {
  singlePermissions: set IndividualReqPermission
}

sig IndividualReqPermission {
  userID: Int,
  thirdPartyID: Int,
  allowed: Bool,
  pending: Bool
} { pending = True implies allowed = False }

sig Run {
  startTime: Int,
  endTime: Int
} { startTime > 0 and startTime < endTime }
 

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

fact IndividualPermissionsBelongToRequestHandler {
  all permission: IndividualReqPermission |
    (some rHandler: RequestHandler | permission in rHandler.singlePermissions)
}

fact IndividualPermissionsThirdPartyUserConnection {
  all permission: IndividualReqPermission |
    (some u: User, tp: ThirdParty | permission.userID = u.IDnumber and permission.thirdPartyID = tp.ID)
}

fact thirdPartyCanAccessOnlyToGrantedData {
  all tp: ThirdParty | (
    all data: tp.userData | (
      some r: IndividualReqPermission | r.userID = data.userID and r.thirdPartyID = tp.ID and r.allowed = True
    )
  )
}

--TODO fact  (no disj sData1, sData2: groupData.data | sData1.userID = sData2.userID )

-- 3 represents the minimum number of data such that it is possible to anonymize it
fact ThirdPartyCanAccessOnlyToAnonymizedGroupData {
  all tp: ThirdParty | (all groupData: tp.groupData | #groupData.data > 3)
}

fact ElderlyAmbulanceConnection {
  all amb: ExtAmbulanceProvider | (
    all old: amb.peopleToRescue | (
      some hStatus: HealthStatus | hStatus.userID = old.IDnumber and
                                                 (hStatus.bloodPressure > old.threshold.bloodPressure or
                                                 hStatus.GSR < old.threshold.GSR or
                                                 hStatus.heartRate > old.threshold.heartRate) and
        (all hStatus2: HealthStatus | hStatus2 != hStatus implies hStatus2.timestamp < hStatus.timestamp)
    )
  )
}

-- 3 is just a constant value representing "now"
fact AthletesAreEnrolledOnlyInFutureRuns {
  all ath: Athlete | (all enRun: ath.enrolledRuns | enRun.startTime > 3)
}

pred showThirdPartyWithUserData {
  some tp: ThirdParty | #tp.userData > 1
  and some permission: IndividualReqPermission | permission.allowed = False
  and no Run and no Athlete and no Elderly
  and #ThirdParty = 1
}

pred showThirdPartyWithGroupData {
  some tp: ThirdParty | #tp.groupData > 0
  and some rHandler: RequestHandler | #rHandler.singlePermissions = 0
  and all gData: GroupData | (some tp: ThirdParty | gData in tp.groupData)
  and no Run and no Athlete and no Elderly
  and #ThirdParty = 1
}

pred showAutomatedSOS {
  some ambulance: ExtAmbulanceProvider | #ambulance.peopleToRescue > 0
  and no Athlete and no Run
  and no ThirdParty and no GroupData
  and one User
}

pred showAthleteEnrolled {
  some ath: Athlete | #ath.enrolledRuns > 0
  and some sRun: Run | sRun.startTime < 3
  and no ThirdParty and no Elderly and no GroupData and no IndividualReqPermission
  and #Athlete > 1
}

-- run showThirdPartyWithUserData for 3
-- run showThirdPartyWithGroupData for 3 but 5 Data
-- run showAutomatedSOS for 3
run showAthleteEnrolled for 3
