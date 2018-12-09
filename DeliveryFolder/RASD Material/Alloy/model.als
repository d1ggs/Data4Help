open util/integer
open util/boolean

abstract sig Data {
  userID: Int,
  timestamp: Int
} { timestamp >= 0 }

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

sig GroupData {
  data: set Data
}

abstract sig Gender {}
one sig Male extends Gender {}
one sig Female extends Gender {}

-- IDnumber: Int used for simplicity, instead of String
sig User {
  IDnumber: Int,
  age: Int,
  gender: Gender
} { IDnumber > 0 and age > 0 }

-- timestamp = 0 used to assign a constant value to thresholds
sig Elderly extends User {
  threshold: HealthStatus
}{ age > 5 and threshold.timestamp = 0 }

-- enrolledRuns: runs in which athlete will participate (in the future)
sig Athlete extends User {
  enrolledRuns: set Run
}

sig ThirdParty {
  ID: Int,
  userData: set Data,
  groupData: set GroupData
} { ID > 0 }

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

fact OnlyThresholdsHaveTimestampZero {
  all data: Data | !(all old: Elderly | old.threshold.userID = data.userID) implies data.timestamp > 0 
}

-- every instance of Data is associated to one user
fact UserDataConnection {
  all data: Data | (some u: User | data.userID = u.IDnumber)
}

-- two health status data related to the same user can't have the same timestamp
-- the same holds for location data
fact DataHaveUniqueTimestamp {
  no disj loc1, loc2: Location | loc1.userID = loc2.userID and loc1.timestamp = loc2.timestamp
  and
  no disj hStatus1, hStatus2: HealthStatus |
    hStatus1.userID = hStatus2.userID and hStatus1.timestamp = hStatus2.timestamp
}

-- every IndividualReqPermission belongs to the RequestHandler
fact IndividualPermissionsBelongToRequestHandler {
  all permission: IndividualReqPermission |
    (some rHandler: RequestHandler | permission in rHandler.singlePermissions)
}

-- every IndividualReqPermission is associated to a User and a ThirdParty
fact IndividualPermissionsThirdPartyUserConnection {
  all permission: IndividualReqPermission |
    (some u: User, tp: ThirdParty | permission.userID = u.IDnumber and permission.thirdPartyID = tp.ID)
}

-- there are no two or more IndividualReqPermission associated to the same User and ThirdParty
fact IndividualPermissionsThirdPartyUserAreUnique {
  no disj perm1, perm2: IndividualReqPermission |
    perm1.userID = perm2.userID and perm1.thirdPartyID = perm2.thirdPartyID
}

-- every ThirdParty has access only to specific users' data
-- for which they have given permission
fact thirdPartyCanAccessOnlyToGrantedData {
  all tp: ThirdParty | (
    all data: tp.userData | (
      some permission: IndividualReqPermission | 
         permission.userID = data.userID and permission.thirdPartyID = tp.ID and permission.allowed = True
    )
  )
}

-- GroupData is a collection of different users' data
fact DataWithinGroupDataBelongToDifferentUsers {
  all groupData: GroupData |
    (no disj sData1, sData2: groupData.data | sData1.userID = sData2.userID) 
}

/*
Every ThirdParty can access only to group data that is anonymized.
The constant '3' represents the minimum number of data such that it is possible to anonymize it.
In this model the procedure that removes personal information from users data is not considered
*/
fact ThirdPartyCanAccessOnlyToAnonymizedGroupData {
  all tp: ThirdParty | (all groupData: tp.groupData | #groupData.data > 3)
}

-- every Elderly, whose last HealthStatus exceed risk thresholds,
-- is in ExtAmbulanceProvider.peopleToRescue
fact ElderlyInNeedAreKnownByExtAmbulanceProvider {
  all old: Elderly | (
    some hStatus: HealthStatus | hStatus.userID = old.IDnumber and
                                                 (hStatus.bloodPressure > old.threshold.bloodPressure or
                                                 hStatus.GSR < old.threshold.GSR or
                                                 hStatus.heartRate < old.threshold.heartRate) and
        (all hStatus2: HealthStatus | hStatus2 != hStatus implies hStatus2.timestamp < hStatus.timestamp)
  ) implies some amb: ExtAmbulanceProvider | old in amb.peopleToRescue
}

-- every Athlete is enrolled only to runs that have not begun yet
-- the constant '3' represents the value "now"
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

run showThirdPartyWithUserData for 3
-- run showThirdPartyWithGroupData for 3 but 5 Data, 5 User
-- run showAutomatedSOS for 3
-- run showAthleteEnrolled for 3
