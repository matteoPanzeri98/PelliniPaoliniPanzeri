
abstract sig Date {}
one sig Monday extends Date {}
one sig Tuesday extends Date {}
one sig Wednesday extends Date {}
one sig Thursday extends Date {}
one sig Friday extends Date {}


abstract sig Hour {
}
one sig Hour_1 extends Hour {}
one sig Hour_2 extends Hour {}
one sig Hour_3 extends Hour {}
one sig Hour_4 extends Hour {}
one sig Hour_5 extends Hour {}
one sig Hour_6 extends Hour {}
one sig Hour_7 extends Hour {}

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
}

sig Suggestion {
	timeSlot: some TimeSlot
}

sig QRReader {

}

sig Unit {
	maxPlaces: Int,
	threshold: Int,
	availableSpots: some AvailableSpot
}{
	maxPlaces > 0
	threshold > 0
	threshold < maxPlaces
}

sig AvailableSpot {
	date: Date,
	startingHour: Hour,
	availablePlaces: Int,
	relatedUnit: one Unit
}{
	availablePlaces >= 0
	availablePlaces <= relatedUnit.maxPlaces
}

sig TimeSlot {
	relatedAvailableSpots: some AvailableSpot,
	startingHour: Hour,
	date: Date
}{
	all avS: AvailableSpot | (avS in relatedAvailableSpots <=> (avS.date = date) && (avS.startingHour = startingHour)) 
		
}

sig NotificationAlert {
	notificationDate: Date,
	notificationHour: Hour
}

fact noReportWithReservationMadeByEmployee {
	all r: Reservation | no rep: Report | #r.employee = 1 and ( r in rep.reservation)
}


//This doesn't involve the employee
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


fact reflexivityOfAvailableSpot {
	availableSpots = ~relatedUnit
}

fact reflexivityOfReservationAndUser {
	user = ~reservationSet
}


//se due timeslot hanno la stessa ora e la stessa data allora appartengono a due stores diversi
/*fact noMultipleTimeSlotsForSameStore{
	all s: Store | no disj ts1, ts2: TimeSlot |	(ts1.relatedAvailableSpots.relatedUnit in s.units and ts2.relatedAvailableSpots.relatedUnit in s.units and
									ts1.date = ts2.date and ts1.startingHour = ts2.startingHour)
}

*/

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

/* Potrebbe essere ridondante
//dato un time slot ogni available spot collegato al time slot è nello stesso supermercato
fact  timeSlotInASingleStore {						
	all ts : TimeSlot | no disj avs1, avs2: AvailableSpot | 	avs1 in ts.relatedAvailableSpots and avs2 in ts.relatedAvailableSpots and
									( some disj s1, s2: Store | avs1 in s1.units.availableSpots and avs2 in s2.units.availableSpots)
}
*/

fact ReservationInSingleStore {
	all r: Reservation| r.acceptedSuggestion.timeSlot.relatedAvailableSpots.relatedUnit in r.chosenStore.units
}

// Stessa cosa di sotto
/* 
//Guarantees that two distinct user don't have the same chosen timeslot in a reservation
fact distinctTimeSlotsForDistinctUsers {
	no ts: TimeSlot | some disj u1, u2: User | ts in u1.reservationSet.chosenTimeSlot and ts in u2.reservationSet.chosenTimeSlot
}
*/

//Se due utenti scelgono gli stessi prodotti da comprare e lo stesso store possono avere la stessa acceptedSuggestion
/*
fact distinctSuggestionsForDistinctReservations {
	no s: Suggestion | some disj r1, r2: Reservation | s in r1.acceptedSuggestion and s in r2.acceptedSuggestion
}
*/

fact timeSlotsRefersToSameUnitsForEachReservation {
	all ts1, ts2: TimeSlot | all r: Reservation | 	(ts1 in r.acceptedSuggestion.timeSlot) && (ts2 in r.acceptedSuggestion.timeSlot) implies 
										ts1.relatedAvailableSpots.relatedUnit = ts2.relatedAvailableSpots.relatedUnit
}

fact coherenceBetweenAcceptedSuggestionAndChosenTimeSlot {
	all r: Reservation | r.chosenTimeSlot in r.acceptedSuggestion.timeSlot
}


//A single user cannot reserve at the same time more than once
assert multipleReservationNotPossible {
	no u: User |	some disj r1, r2: Reservation | r1 in u.reservationSet and r2 in u.reservationSet 
				and r1.chosenTimeSlot.startingHour = r2.chosenTimeSlot.startingHour 
				and r1.chosenTimeSlot.date = r2.chosenTimeSlot.date
}

//check multipleReservationNotPossible for 4

pred show {
	#TimeSlot = 2
	#AvailableSpot = 1
}


run show for 5

