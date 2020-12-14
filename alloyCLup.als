sig Store {
	qrReader: some QRReader,	//Fact: ci sono almeno 2 QRreader per store
	units: some Unit
}{ 
	#qrReader > 1 
}

sig Date {
	day: one Int
}{
	day > 0
}

sig Hour {
	hour: Int,
	minute: Int
}{
	hour >= 0
	hour <= 23
	minute >= 0
	minute <= 59
}

sig User {
	name: String,
	surname: String,
	email: String,
	password: String,
	reservationSet: set Reservation
}{
	all r1, r2: Reservation |( (r1 in reservationSet) && (r2 in reservationSet) <=> (r1.chosenTimeSlot.date != r2.chosenTimeSlot.date) || 
			((mul[r1.chosenTimeSlot.startingHour.hour,60] + r1.chosenTimeSlot.startingHour.minute) >
			 ((mul[r2.chosenTimeSlot.startingHour.hour,60] + r2.chosenTimeSlot.startingHour.minute)  + r2.estimatedTime)) && 
			(r1.chosenTimeSlot.date = r2.chosenTimeSlot.date))
}

sig Employee extends User {

}

sig Reservation {
	qrCode: String,
	acceptedSuggestion: one Suggestion,
	notification: one NotificationAlert,
	chosenStore: one Store,
	user: one User,
	chosenTimeSlot: one TimeSlot,
	estimatedTime: one Int
}

sig LineUpRequest extends Reservation {
	
}

sig Report {
	reservation: one Reservation,
	qrReader1: one QRReader,
	qrReader2: one QRReader,
	entranceHour: one Hour
}

sig Suggestion {
	timeSlot: some TimeSlot
}

sig QRReader {

}

sig Unit {
	name: String,
	maxPlaces: Int,
	threshold: Int,
	availableSpots: some AvailableSpot
}{
	maxPlaces > 0
	threshold > 0
}

sig AvailableSpot {
	date: Date,
	startingHour: Hour,
	availablePlaces: Int,
	relatedUnit: Unit
}{
	availablePlaces >= 0
}

sig TimeSlot {
	relatedAvailableSpots: some AvailableSpot,
	startingHour: Hour,
	date: Date
}{
	all avS: AvailableSpot | (avS in relatedAvailableSpots <=> (avS.date = date) && (avS.startingHour = startingHour)) 
		
}

sig NotificationAlert {
	date: Date,
	notificationHour: Hour
}

fact noSharedQrReader {
	all s1,s2:Store | no q: QRReader  | (s1 != s2) => (q in s1.qrReader && q in  s2.qrReader) 
 }

fact noSharedUnit {
	all s1,s2:Store | no u: Unit  | (s1 != s2) => (u in s1.units && u in s2.units) 
 }

//se due timeslot hanno la stessa ora e la stessa data allora appartengono a due stores diversi
fact noMultipleTimeSlotsForSameStore{
	all ts1,ts2 : TimeSlot | all  s1,s2: Store| (ts1.relatedAvailableSpots.relatedUnit in s1.units and ts2.relatedAvailableSpots.relatedUnit in s2.units  and 
		ts1.date = ts2.date && ts1.startingHour=ts2.startingHour) => (s1 != s2)
}



//dato un time slot ogni aviable spot collegato al time slot è nello stesso supermercato
fact  timeSlotInASingleStore {						
	all ts : TimeSlot | all avS: AvailableSpot | avS in ts.relatedAvailableSpots => ( one s:Store | some u:Unit | u in s.units && avS in u.availableSpots )
}

pred show {}

run show for 8
