open util/relation
open util/boolean

//----SIGNATURES----
// User's role: it can be a student or a company
abstract sig Role {}
sig Student extends Role {
	applications: some Application,
	cv: one CV
}
sig CV{}
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
	all s: Student | one u: User | 
		s in u.role 
	and
    	all c: Company |  one u: User | 
		c in u.role 
}

//DoubleArrowConstraint
fact DoubleAssociation {
	//An application can only be associated with a student
    	all a: Application | one s: Student | 
    		s in a.submittedBy and 
		a in s.applications and
    		s.applications.submittedBy=s 
    	//An application can only be associated with a Intenship
    	all a: Application | one i: Internship | 
    		a in i.applicants and  
		i in a.relatedTo and
    		i.applicants.relatedTo = i
    	//An internship can only be associated with a Company
    	all  i:Internship | one c: Company | 
    		c in i.postedBy and 
		i in c.postings and 
    		c.postings.postedBy = c  
}

//Unique Description, CV, and Interview 
fact UniqueItems {
	//description
    	all i1, i2: Internship | i1 != i2 implies
   		i1.description != i2.description
    	all dd: Description | one ii:Internship | 
		dd in ii.description
	//CV
    	all s1,s2: Student| s1 != s2 implies
		s1.cv != s2.cv
    	all ccvv:CV | one ss: Student |  
		ccvv in ss.cv
    	//interview
   	 all a1,a2: Application | a1!=a2 implies 
   		a1.interviews != a2.interviews
    	all i: Interview | one a: Application |
		 i in a.interviews
}

//Unique Application
fact UniqueApplications{
	all i1, i2: Internship | i1 != i2 implies 
    		#(i1.applicants & i2.applicants) <= 0
    	all c1, c2: Company | c1 != c2 implies 
    		#(c1.postings & c2.postings) <= 0
    	all s1,s2: Student | s1 !=s2 implies 
    		#(s1.applications & s2.applications) <=0
}

// A student can make only an application for one internship
fact UniqueApplicationsPerStudent {
	all s: Student | all i: Internship | 
    		#(s.applications & i.applicants) <= 1
}

//A role cannot have a mettengs the same day
fact SameDayMeetings {
	all ss1,ss2: Student | all cc1,cc2: Company |
   	all a1,a2: Application | a1!=a2 and
   		((ss1 in a1.submittedBy and 
		   ss2 in a2.submittedBy and
   		   cc1 in a1.relatedTo.postedBy and
		   cc1 in a1.relatedTo.postedBy)
   	or
   		 (ss1 in a1.submittedBy and 
		  ss1 in a2.submittedBy and
   		  cc1 in a1.relatedTo.postedBy and 
		  cc2 in a1.relatedTo.postedBy))
   	implies a1.interviews.schedule != a2.interviews.schedule
}

// Interview process
fact InterviewProess{ 
	all a: Application | 
        	always( a.interviews.outcome = InProgress 
			implies a.status = Pending)
	 	and always(a.interviews.outcome = Passed 
			implies a.status = Accepted)
		and always(a.interviews.outcome = Failed 
			implies a.status = Rejected)
}


//-------------------------------------------------------------------------------------------

//----ASSERTIONS----
// Assertion to verify the correctness of the user structure as:
assert VerifyUserStructure{
	//mail and personal info
    	all u1, u2: User | u1 != u2 implies 
    		u1.email != u2.email and  
		u1.otherInformation != u2.otherInformation
	//role
    	all s: Student | one u: User | u.role = s
    	all c: Company | one u: User | u.role = c
}
check VerifyUserStructure

//Assertion to verify DoubleArrowConstraint
assert VerifyDoubleAssociation {
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
	//Unique Description, CV, and Interview 
    	all i1, i2: Internship | i1 != i2 implies 
		i1.description != i2.description
    	all dd: Description | one ii:Internship | 
		dd in ii.description
    	all s1,s2: Student| s1 != s2 implies s1.cv != s2.cv
    	all ccvv:CV | one ss: Student |  ccvv in ss.cv
    	all a1,a2: Application | a1!=a2 implies 
		a1.interviews != a2.interviews
    	all i: Interview | one a: Application |
		i in a.interviews
    	//Unique Application
   	 all i1, i2: Internship | i1 != i2 implies 
   	#(i1.applicants & i2.applicants) <= 0
   	all c1, c2: Company | c1 != c2 implies 
   	#(c1.postings & c2.postings) <= 0
   	all s1,s2: Student | s1 !=s2 implies 
    	#(s1.applications & s2.applications) <=0
   	//Student can make only 1 application for 1 internship
    	all s: Student | all i: Internship | 
    	#(s.applications & i.applicants) <= 1
}
check VerifyInternshipStructures

//Two meetings cannot be in the same day if:
assert VerifyInterviewStructures {
	all ss1,ss2: Student | all cc1,cc2: Company |
   	all a1,a2: Application | a1!=a2 and
		//are carried by the same company
   		((ss1 in a1.submittedBy and 
		   ss2 in a2.submittedBy and
   		   cc1 in a1.relatedTo.postedBy and
		   cc1 in a1.relatedTo.postedBy)
   	or
		//are carried by the same student
   		 (ss1 in a1.submittedBy and 
		  ss1 in a2.submittedBy and
   		  cc1 in a1.relatedTo.postedBy and 
		  cc2 in a1.relatedTo.postedBy))
   	implies a1.interviews.schedule != a2.interviews.schedule
  	//meetings have a schedule if a student submits them
   	all a: Application | a.interviews.schedule != none 
   		 implies a.submittedBy in Student
}
check VerifyInternshipStructures

//Check interview process
assert InterviewProocess{
    all a: Application | 
	//Failed => Rejected
        some i: a.interviews | i.outcome = Failed 
		implies a.status = Rejected
	and 
	//Passed => Accepted
       some i: a.interviews | i.outcome = Passed 
		implies a.status = Accepted
	and
	//InProgress => Pending
       some i: a.interviews | i.outcome = InProgress 
		implies a.status = Pending
}
check InterviewProocess

//----STATIC MODELS----
//one student and one company
pred oneStudentOneCompanyOneInternship {
    #Student = 1
    #Company = 1
    #Internship = 1
}
run oneStudentOneCompanyOneInternship  for 2

//two students and one company
pred twoStudentOneCompanyOneInternship {
    #Student = 2
    #Company = 1
    #Internship = 1
}
run twoStudentOneCompanyOneInternship for 3

//one student and one two compaanies
pred oneStudentTwoCompanyThreeInternship {
    #Student = 1
    #Company = 2
    #Internship = 3
}
run oneStudentTwoCompanyThreeInternship for 3 

//----DYNAMIC MODELS----
//passed interview
pred interviewPassed[ap:Application, s:Student, c:Company]{
	ap.interviews.outcome = InProgress ; 
	ap.interviews.outcome = Passed
	#Student = 1
    	#Company = 1
    	#Internship = 1
}
run interviewPassed for 2  

//failed interview
pred interviewRejected[ar:Application, s:Student, c:Company]{
	ar.interviews.outcome = InProgress ; 
	ar.interviews.outcome = Failed
	#Student = 1
    	#Company = 1
    	#Internship = 1
}
run interviewRejected for 2  

