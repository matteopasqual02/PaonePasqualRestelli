open util/relation
open util/boolean

//----SIGNATURES----
// User's role: it can be a student or a company
abstract sig Role {}
sig Student extends Role {
    applications: some Application
}
sig Company extends Role {
    postings: some Internship
}

// Users' personal information
sig User {
    email: one Email,
    otherInformation: one PersonalData,
    role: one Role
}
sig Email{}
sig PersonalData{}

// Internship
sig Internship {
    postedBy: one Company,
     applicants: some Application,
    description: one Description,
}
sig Description{}

// Application for an internship
sig Application {
    submittedBy: one Student,
    relatedTo: one Internship,
    interviews: one Interview,
    var status:  Status
}
enum Status {Pending, Accepted, Rejected}

// Interview
sig Interview {
    schedule: one DateTime,
    var outcome:  Outcome
}
enum Outcome {Passed, Failed, InProgress}
sig DateTime{}

//----FACTS----
// No two Users can have the same email or personal info
fact UniqueUsersEmailsAndPersonalInfo {
    all u1, u2: User | u1 != u2 implies
    u1.email != u2.email and
    u1.otherInformation != u2.otherInformation
}

// A role can only be associated with one User
fact OneUserPerStudentAndCompany{
    all s: Student | one u: User | u.role = s and
    all c: Company |  one u: User | u.role = c
}

//DoubleArrowConstraint
fact DoubleAssociation {
    //An interview can only be associated with an application
    all i: Interview | one a: Application | 
    i in a.interviews
   //An application can only be associated with a student
   all a: Application | one s: Student | 
   s in a.submittedBy and a in s.applications and
   s.applications.submittedBy=s
   //An application can only be associated with a Intenship
    all a: Application | one i: Internship | 
    a in i.applicants and  i in a.relatedTo and
    i.applicants.relatedTo = i
    //An internship can only be associated with a Company
    all  i:Internship | one c: Company | 
    c in i.postedBy and i in c.postings and 
    c.postings.postedBy = c  
}

// A student can make only an application for one internship
fact UniqueApplicationsPerStudent {
    all s: Student | all i: Internship | 
    #(s.applications & i.applicants) <= 1
}

// All applications are related to real posted Internship
fact ApplicationLinkedToValidInternship {
    all a: Application | a.relatedTo.postedBy in Company
}

//Two internships cannot have the same description 
fact UniqueInternshipsPerCompany {
    all i1, i2: Internship | i1 != i2 implies 
    i1.description != i2.description
}

//Two students cannot have the same application
fact UniqueApplicationsPerStudent {
    all s1,s2: Student | s1!=s2 implies 
    s1.applications != s2.applications
}

// All applications that are scheduled are applications that are really submitted by a student
fact InterviewApplicationRelation {
    all a: Application | a.interviews.schedule != none 
    implies a.submittedBy in Student
}

//A role cannot have a mettengs the same day
fact SameDayMeetings {
   all ss1,ss2: Student | all cc1,cc2: Company |
   all a1,a2: Application | a1!=a2 and
   ((ss1 in a1.submittedBy and ss2 in a2.submittedBy and
   cc1 in a1.relatedTo.postedBy and cc1 in a1.relatedTo.postedBy)or
  (ss1 in a1.submittedBy and ss1 in a2.submittedBy and
  cc1 in a1.relatedTo.postedBy and cc2 in a1.relatedTo.postedBy))
  implies a1.interviews.schedule != a2.interviews.schedule
}

fact InitialApplicationStatus {
    all a: Application | a.status = Pending
}
fact InitialInterviewOutcome {
    all i: Interview | i.outcome = InProgress
}

//-------------------------------------------------------------------------------------------

//----ASSERTIONS----
// Assertion to verify the correctness of the user structure as:
assert VerifyUserStructure{
    all u1, u2: User | u1 != u2 implies 
    u1.email != u2.email and  u1.otherInformation != u2.otherInformation
    all s: Student | one u: User | u.role = s
    all c: Company | one u: User | u.role = c
}
check VerifyUserStructure

//Assertion to verify DoubleArrowConstraint
assert VerifyDoubleAssociation {
     //An interview can only be associated with an application
    all i: Interview | one a: Application | 
    i in a.interviews
   //An application can only be associated with a student
   all a: Application | one s: Student | 
   s in a.submittedBy and a in s.applications and
   s.applications.submittedBy=s
   //An application can only be associated with a Intenship
    all a: Application | one i: Internship | 
    a in i.applicants and  i in a.relatedTo and
    i.applicants.relatedTo = i
    //An internship can only be associated with a Company
    all  i:Internship | one c: Company | 
    c in i.postedBy and i in c.postings and 
    c.postings.postedBy = c  
}
check VerifyDoubleAssociation

// Assertion to verify all Internship application structure
assert VerifyInternshipStructures {
    // Students can make only one application for each internship
    all s: Student | all i: Internship | 
    #(s.applications & i.applicants) <= 1
    //All applications are related to valid posted internships
    all a: Application | a.relatedTo.postedBy in Company
    // A company can't publish two equal internships 
    all i1, i2: Internship | i1 != i2 implies i1.description != i2.description
    //All scheduled interviews are actually submitted 
    all a: Application | a.interviews.schedule != none implies a.submittedBy in Student
   //Two students cannot have the same application
    all s1,s2: Student | s1!=s2 implies s1.applications != s2.applications
    // meetings strudent side
    all ss1,ss2: Student | all cc1,cc2: Company |
    all a1,a2: Application | a1!=a2 and
   ((ss1 in a1.submittedBy and ss2 in a2.submittedBy and
    cc1 in a1.relatedTo.postedBy and cc1 in a1.relatedTo.postedBy)or
   (ss1 in a1.submittedBy and ss1 in a2.submittedBy and
   cc1 in a1.relatedTo.postedBy and cc2 in a1.relatedTo.postedBy))
   implies a1.interviews.schedule != a2.interviews.schedule
}
check VerifyInternshipStructures

//one student and one company
run {} for 2 but exactly 1 Student, exactly 1 Company, exactly 1  Internship

//two students and one company
run {} for 3 but exactly 2 Student, exactly 1 Company, exactly 1  Internship, exactly 1 Description

//one student and one company
run {} for 3 but exactly 1 Student, exactly 2 Company, exactly 3  Application
