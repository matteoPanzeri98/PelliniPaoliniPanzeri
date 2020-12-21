abstract sig Date {
	prec: lone Date
}
one sig Monday extends Date {}{ prec = none}
one sig Tuesday extends Date {}{ prec = Monday }
one sig Wednesday extends Date {}{ prec = Tuesday }
one sig Thursday extends Date {}{ prec = Wednesday }
one sig Friday extends Date {}{ prec = Thursday }


abstract sig Hour {
	precHour: lone Hour
}
one sig Hour_1 extends Hour {}{precHour = none}
one sig Hour_2 extends Hour {}{precHour = Hour_1 }
one sig Hour_3 extends Hour {}{precHour = Hour_2 }
one sig Hour_4 extends Hour {}{precHour = Hour_3 }
one sig Hour_5 extends Hour {}{precHour = Hour_4 }
one sig Hour_6 extends Hour {}{precHour = Hour_5 }
one sig Hour_7 extends Hour {}{precHour = Hour_6 }

sig Store {
	qrReader: some QRReader,
	units: some Unit
}{ 
	#qrReader > 1 
}


sig User {
	reservationSet: set Reservation
}

sig Employee {
	store: one Store
}

sig Reservation {
	acceptedSuggestion: one Suggestion,
	notification: one NotificationAlert,
	chosenStore: one Store,
	user: lone User,
	employee: lone Employee,
	chosenTimeSlot: one TimeSlot,
}{
	notification.notificationHour = chosenTimeSlot.startingHour
	notification.notificationDate = chosenTimeSlot.date
	#user = 1 <=> #employee = 0
}

sig LineUpRequest extends Reservation {}
{let x = acceptedSuggestion.timeSlot | #x = 1}

sig Report {
	reservation: one Reservation,
	qrReader1: one QRReader,
	qrReader2: one QRReader,
	entranceHour: one Hour
}{
	qrReader1 != qrReader2
	entranceHour = reservation.chosenTimeSlot.startingHour 	//User are expected to be on time
}

sig Suggestion {
	timeSlot: some TimeSlot
}

sig QRReader {

}

sig Unit {
	maxPlaces: Int,
	availableSpots: some AvailableSpot
}{
	maxPlaces  = 3
}

sig AvailableSpot {
	date: Date,
	startingHour: Hour,
	relatedUnit: one Unit
}

sig TimeSlot {
	relatedAvailableSpots: some AvailableSpot,
	startingHour: Hour,
	date: Date
}{
	all avS: AvailableSpot | (avS in relatedAvailableSpots => (avS.date = date) && (avS.startingHour = startingHour)) 
		
}

sig NotificationAlert {
	notificationDate: Date,
	notificationHour: Hour
}

fact noReportWithReservationMadeByEmployee {
	all r: Reservation | no rep: Report | #r.employee = 1 and ( r in rep.reservation)
}

fact employeeDoesntMakeRequestsToOtherStore {
	all r: Reservation | #r.employee = 1 implies r.chosenStore = r.employee.store
}

fact noMultipleReservationAtTheSameTimeForSingleUser {
	all u: User | no disj r1, r2: Reservation | 	(r1 in u.reservationSet and r2 in u.reservationSet 
									and r1.chosenTimeSlot.date = r2.chosenTimeSlot.date 
									and r1.chosenTimeSlot.startingHour = r2.chosenTimeSlot.startingHour)
}

fact noSharedQrReader {
	all disj s1,s2: Store | no q: QRReader  | (q in s1.qrReader && q in  s2.qrReader) 
 }

fact noSharedUnit {
	all u: Unit | no disj s1,s2: Store  | (u in s1.units && u in s2.units) 
 }

fact  noSharedAvailableSpotsAmongUnits {
	all avS: AvailableSpot | no disj u1, u2: Unit | avS in u1.availableSpots and avS in u2.availableSpots
}

//We can't have more than one spot in an hour for a specific unit
fact oneAvailableSpotPerHour {
	all u: Unit | no disj avs1, avs2: AvailableSpot | (avs1 in u.availableSpots) and (avs2 in u.availableSpots) and 
										(avs1.date = avs2.date) and (avs1.startingHour = avs1.startingHour)
}

//notification is injective
fact oneReservationPerNotification {
	no disj r1, r2: Reservation | r1.notification = r2.notification 
}

//reservation is injective
fact oneReportPerReservation {
	no disj rep1, rep2: Report | rep1.reservation = rep2.reservation
}

fact oneReservationPerSuggestion {
	no disj r1, r2: Reservation | r1.acceptedSuggestion = r2.acceptedSuggestion
}


fact reflexivityOfAvailableSpot {
	availableSpots = ~relatedUnit
}

fact reflexivityOfReservationAndUser {
	user = ~reservationSet
}


//se due timeslot hanno la stessa ora e la stessa data allora appartengono a due stores diversi
fact noMultipleTimeSlotsForSameStore{
	all r: Reservation | no disj ts1, ts2: TimeSlot |	ts1 in r.acceptedSuggestion.timeSlot and 	ts2 in r.acceptedSuggestion.timeSlot and
										ts1.relatedAvailableSpots.relatedUnit in r.chosenStore.units and ts2.relatedAvailableSpots.relatedUnit in r.chosenStore.units and
										ts1.date = ts2.date and ts1.startingHour = ts2.startingHour
}

fact noMultipleEmployeeForSameStore {
	no disj e1, e2: Employee | e1.store = e2.store
}

fact noStoreWithoutReservation {
	no s: Store | all r: Reservation | s not in r.chosenStore
}

fact noNotificationWithoutReservation {
	no n: NotificationAlert | all r: Reservation | n not in r.notification
}


fact noUnitWithoutRelatedStore {
	all u: Unit | some s: Store | u  in s.units
}

fact noTimeSlotWithoutSuggestion {
	all ts: TimeSlot | some s: Suggestion | ts in s.timeSlot
}

fact noSuggestionWithoutReservation {
	all s: Suggestion | some r: Reservation | s in r.acceptedSuggestion
}

fact noAvailableSpotWithoutTimeSlot {
	all avs: AvailableSpot | some ts: TimeSlot | avs in ts.relatedAvailableSpots
}	

fact ReservationInSingleStore {
	all r: Reservation| r.acceptedSuggestion.timeSlot.relatedAvailableSpots.relatedUnit in r.chosenStore.units
}

fact timeSlotsRefersToSameUnitsForEachReservation {
	all ts1, ts2: TimeSlot | all r: Reservation | 	(ts1 in r.acceptedSuggestion.timeSlot) && (ts2 in r.acceptedSuggestion.timeSlot) implies 
										ts1.relatedAvailableSpots.relatedUnit = ts2.relatedAvailableSpots.relatedUnit
}

fact coherenceBetweenAcceptedSuggestionAndChosenTimeSlot {
	all r: Reservation | r.chosenTimeSlot in r.acceptedSuggestion.timeSlot
}

fact noRedundantTimeSlots {
	no disj ts1, ts2: TimeSlot | ts1.startingHour = ts2.startingHour and ts1.date = ts2.date and ts1.relatedAvailableSpots = ts2.relatedAvailableSpots
}

fact noReportOnSubsequentDays {
	let prec_tran = ^prec | all r1: Reservation | 	(one rep: Report, d: Date | rep.reservation = r1 and d = r1.chosenTimeSlot.date) implies 
										(all r2: Reservation | (r2.chosenTimeSlot.date in r1.chosenTimeSlot.date.prec_tran) implies 
										(one rep2: Report | rep2.reservation = r2))
}

fact noReportOnSubsequentHours {
	let precHour_tranRef = *precHour | all r1: Reservation | 	(one rep: Report | rep.reservation = r1) implies 
												(all r2: Reservation | (r2.chosenTimeSlot.date = r1.chosenTimeSlot.date and 
												(r2.chosenTimeSlot.startingHour in r1.chosenTimeSlot.startingHour.precHour_tranRef) 
												implies (one rep1: Report | rep1.reservation = r2)))
}

fact maxAmountOfPeopleInTheStore {
	//no avs: AvailableSpot |  #{r: Reservation | avs in r.chosenTimeSlot.relatedAvailableSpots} > 3

	no avs: AvailableSpot |  #{r: Reservation | avs in r.acceptedSuggestion.timeSlot.relatedAvailableSpots} > 3
}


//A single user cannot reserve at the same time more than once
assert multipleReservationNotPossible {
	no u: User |	some disj r1, r2: Reservation | r1 in u.reservationSet and r2 in u.reservationSet 
				and r1.chosenTimeSlot.startingHour = r2.chosenTimeSlot.startingHour 
				and r1.chosenTimeSlot.date = r2.chosenTimeSlot.date
}

//check multipleReservationNotPossible for 4


assert maxPlacesCannotBeExceeded{
	no disj r1, r2, r3, r4: Reservation | some avs: AvailableSpot | 	avs in r1.chosenTimeSlot.relatedAvailableSpots and
																avs in r2.chosenTimeSlot.relatedAvailableSpots and
																avs in r3.chosenTimeSlot.relatedAvailableSpots and
																avs in r4.chosenTimeSlot.relatedAvailableSpots
}

//check maxPlacesCannotBeExceeded for 5



/* PREDICATES */

/**
	A user reserves or makes multiple requests to line up. 
	It is possible to make requests in more than one store, in this case 2 store.
	A user cannot make multiple requests for the same hour and date, even if they are in different stores
	On the other hand, multiple users can make requests in the same timeslot.
	In this case, it is shown the latter situation
*/
pred reservationOrLiningUpByTheApp {
	#Store = 2
	#User = 2
	#Employee = 0
	some disj r1, r2: Reservation | r1.user != r2.user and r1.chosenTimeSlot = r2.chosenTimeSlot
}

//run reservationOrLiningUpByTheApp for 5

/**
	An employee in the store act as a proxy and reserves or makes requests in place of clients. 
	It is possible for him/her to reserve in the same timeslot for multiple requests.
	In this example, an employee reserves for three times in the same timeslot.
	The multiplicity of Suggestions related to the same TimeSlot is to be noted too.
	There can be multiple employee related to a single store
*/ 
pred reservationOrLiningUpByTheStore {
	#Employee = 2
	#User = 0
	#Store = 1
	#TimeSlot = 1
	#Reservation = 3
}

//run reservationOrLiningUpByTheStore for 5

/**
	A more general situation.
	
*/
pred mixedRequests {
	#Store = 2
	#User = 2
	#Employee = 2
	#Reservation = 5
	some disj r1, r2: Report | r1.reservation.chosenTimeSlot.date != r2.reservation.chosenTimeSlot.date 
}

run mixedRequests for 5

pred showMaxPlaces {
	#Store = 1
	#TimeSlot = 2
	#AvailableSpot = 3
	all disj a1, a2: AvailableSpot | a1.date = a2.date and a1.startingHour = a2.startingHour
}

//run showMaxPlaces for 6



