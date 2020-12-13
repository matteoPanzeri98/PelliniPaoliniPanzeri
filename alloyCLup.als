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
	all r1, r2: Reservation |( (r1 in reservationSet) && (r2 in reservationSet) <=> (r1 != r2) )
}

sig Employee extends User {

}

sig Reservation {
	qrCode: String,
	acceptedSuggestion: one Suggestion,
	notification: one NotificationAlert,
	chosenStore: one Store,
	user: one User
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

sig Timeslot {
	relatedAvailableSpots: some AvailableSpot,
	startingHour: Hour,
	date: Date
}{
	all avS: AvailableSpot |
		 (avS in relatedAvailableSpots <=> (avS.date = date) && (avS.startingHour = startingHour))
}

sig NotificationAlert {
	date: Date,
	notificationHour: Hour
}



pred show {
}

run show for 8
