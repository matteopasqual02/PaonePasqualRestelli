open util/relation
open util/boolean

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
    otherInformation: lone PersonalData,
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

// Fact to ensure no two Users have the same email
fact UniqueUsersEmails {
    all u1, u2: User | u1 != u2 implies u1.email != u2.email
}

// Fact to ensure a Student or a Company can only be associated with one User
fact OneUserPerStudentAndCompany{
    all s: Student | one u: User | u.role = s and
    all c: Company |  one u: User | u.role = c
}

run {} for 7 but exactly 2 Student, exactly 1 Company, exactly 1 Interview, exactly 3 User, exactly 1  Internship,  exactly 1  Application
