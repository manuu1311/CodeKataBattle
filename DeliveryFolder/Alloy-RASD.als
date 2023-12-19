-- Alloy model for CodeKataBattle platform


// SIGNATURES

-- Time is used to represent a couple <date,time>
sig Time {
  value: one Int,     -- Value of the <data, time> couple
}

-- Signature representing a user in the system
abstract sig User {
  userId: one Int,                  -- Unique identifier for a user
  username: lone String,       -- User's username
  email: one String,              -- User's email address
  password: one String,        -- User's password
}
sig Educator extends User {}
sig Student extends User {
  badges: some Badge          -- Student's badges
}

-- Signature representing a code kata for programming exercises
sig CodeKata {
  kataId: one Int,                                 -- Unique identifier for a code kata
  description: lone String,                    -- Description of the programming exercise
  programmingLanguage: lone String,   -- Programming language for the exercise
}

-- Signature representing a tournament organized by an educator
sig Tournament {
  tournamentId: one Int,         -- Unique identifier for a tournament
  educators: some Educator,   -- Educator organizing the tournament and Educators managing the tournament
  battles: set Battle,                -- Set of battles within the tournament
  badges: some Badge           -- Some badges that could be associated with the tournament
}

-- Signature representing a battle within a tournament
sig Battle {
  battleId: one Int,                       -- Unique identifier for a battle
  codeKata: one CodeKata,           -- Code kata for the battle
  tournament: one Tournament,    -- Tournament associated to the battle
  teams: set Team,                      -- Set of teams participating in the battle
  maxTeamSize: one Int,              --Max Number of Students allowed in a team
  minTeamSize: one Int,               --Min Number of Students allowed in a team
  registrationDeadline: one Time,  -- Deadline for team registration
  submissionDeadline: one Time   -- Deadline for code submission
}

-- Signature representing a team participating in a battle
sig Team {
  teamId: one Int,                   -- Unique identifier for a team
  members: set Student,          -- Set of users in the team
  submissions: set Submission -- Set of submissions of the team
  
}

-- Signature representing a code submission by a team
sig Submission {
  submissionId: one Int,     -- Unique identifier for a submission
  team: one Team,             -- Team that submitted the code
  code: lone String,           -- Code submitted by the team
  timestamp: one Time       -- Timestamp of the submission
}

sig Badge {
  badgeId: one Int,  -- Unique identifier for a badge
  description: one String  -- Description of the badge
}










// FACTS

-- Fact spcifying time constraint
fact TimeContraints{
  all t: Time |
    t.value > 0
   and
  (all disj t1, t2: Time |
    t1.value != t2.value)
}

-- Fact specifying constraints on user attributes
fact UserConstraints {
  (all u: User |
    u.userId > 0 and
    u.email != none and
    u.password != none)
  (all disj u1, u2: User |
     u1.email != u2.email and 
     u1.username != u2.username and
     u1.userId != u2.userId)
  (all s: Student |
     #s.badges >= 0)
}

-- Fact specifying constraints on code kata attributes
fact CodeKataConstraints {
  (all ck: CodeKata |
    ck.kataId > 0 and
    ck.description != none and
    ck.programmingLanguage != none)
  and
  (all disj ck1, ck2: CodeKata |
    ck1.kataId != ck2.kataId)
}

-- Fact specifying constraints on tournament attributes
fact TournamentConstraints {
  (all t: Tournament |
    t.tournamentId > 0 and
    t.educators != none and
    #t.battles >= 0)
  and
  (all disj t1, t2: Tournament |
    t1.tournamentId != t2.tournamentId)
}

-- Fact specifying constraints on battle attributes
fact BattleConstraints {
  all b: Battle |
    b.battleId > 0 and
    b.codeKata != none and
    b.teams != none and
    b.registrationDeadline != none and
    b.submissionDeadline != none 
  and
  (all disj b1, b2: Battle |
    b1.battleId != b2.battleId)
}

-- Fact specifying constraints on team attributes
fact TeamConstraints {
  all t: Team |
    t.teamId > 0 and
    t.members != none and
    t in Battle.teams
  and
  (all disj t1, t2: Team |
    t1.teamId != t2.teamId)
}

-- Fact specifying constraints on submission attributes
fact SubmissionConstraints {
  (all s: Submission |
    s.submissionId > 0 and
    s.team != none and
    s.code != none and
    s.timestamp != none and
    (all t: Team | 
    s in t.submissions iff s.team = t))
  (all disj s1, s2: Submission |
    s1.submissionId != s2.submissionId
    and 
    (s1.team = s2.team implies s1.timestamp != s2.timestamp))
}



-- Fact specifying constraints on submission attributes
fact BadgeConstraints {
  all b: Badge |
    b.badgeId > 0 and
    b.description != none
  and
  (all disj b1, b2: Badge |
    b1.badgeId != b2.badgeId)
}

-- Fact specifying the contraint  of the team size in a battle
fact TeamInBattleConstraints {
  all b: Battle |
    all t: b.teams |
      #t.members <= b.maxTeamSize and
      #t.members >= b.minTeamSize
}

-- Fact specifying the constraint of the size of teams
fact SizeOfTeamsContraints {
  all b: Battle |
    b.minTeamSize >= 1 and
    b.maxTeamSize >= 1
}

-- Fact specifying the membership of the student to a single team in the scope of a battle
fact MembershipOfStudentConstraints {
  (all b: Battle |
    all disj t1, t2: b.teams |
      all s: t1.members |
        s not in t2.members)
}

-- Fact specifying the time constraint between registration and submission deadlines
fact RegistrationSubmissionContraints {
  (all b: Battle |
    b.registrationDeadline.value < b.submissionDeadline.value)
}






// ASSERTIONS

-- Assertion: All users have unique user IDs
assert UniqueUserIDs {
  all u1, u2: User | u1 != u2 implies u1.userId != u2.userId
}

-- Assertion: All code katas have unique IDs
assert UniqueKataIDs {
  all ck1, ck2: CodeKata | ck1 != ck2 implies ck1.kataId != ck2.kataId
}

-- Assertion: All tournaments have unique IDs
assert UniqueTournamentIDs {
  all t1, t2: Tournament | t1 != t2 implies t1.tournamentId != t2.tournamentId
}

-- Assertion: All battles have unique IDs
assert UniqueBattleIDs {
  all b1, b2: Battle | b1 != b2 implies b1.battleId != b2.battleId
}

-- Assertion: All teams have unique IDs
assert UniqueTeamIDs {
  all t1, t2: Team | t1 != t2 implies t1.teamId != t2.teamId
}

-- Assertion: All submissions have unique IDs
assert UniqueSubmissionIDs {
  all s1, s2: Submission | s1 != s2 implies s1.submissionId != s2.submissionId
}

-- Assertion: All team members are distinct
assert DistinctTeamMembers {
  all t: Team | no disj u1, u2: t.members | u1 != u2
}

-- Assertion: CodeKata associated with a battle must be unique
assert UniqueCodeKataPerBattle {
  all b: Battle | all disj ck1, ck2: b.codeKata | ck1 != ck2
}

-- Assertion: Submission timestamp is within the battle deadlines
assert SubmissionWithinDeadlines {
  all b: Battle, s: Submission | s in b.teams.submissions implies
    b.registrationDeadline.value <= s.timestamp.value and
    s.timestamp.value <= b.submissionDeadline.value
}


-- Assertion: Each team in a battle has a distinct set of members
assert DistinctTeamMembersInBattle {
  all b: Battle | all t1, t2: b.teams | t1 != t2 implies no t1.members & t2.members
}

-- Assertion: All battles within a tournament have distinct IDs
assert UniqueBattlesPerTournament {
  all t: Tournament | all disj b1, b2: t.battles | b1 != b2
}





// PREDICATES

-- Predicate representing the action of a user registering for a battle
pred RegisterForBattle[student: Student, battle: Battle] {
  student in battle.teams.members
}

-- Predicate representing the evaluation of a code submission in a battle
pred EvaluateSubmission[battle: Battle, submission: Submission] {
  submission in battle.teams.submissions
}

run show{} for 3 but exactly 20 String
