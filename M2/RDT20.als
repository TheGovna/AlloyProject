module project/m2
open util/ordering [State]

abstract sig Response {}
one sig ACK, NAK extends Response {}

abstract sig CheckSum {}
one sig Correct, Error extends CheckSum {}

sig Packet {}

sig State {
	senderData: set Packet,
	receiverData: set Packet,
	sentPacket: lone Packet,
	tempSentPacket: lone Packet,  // version of packet that sender saves to resend if necessary
	checkSum: lone CheckSum,
	response: lone Response
} 
{
	no p :Packet | p in senderData and p in receiverData
	all p: Packet | p in senderData or p in receiverData or p = tempSentPacket
}

pred State.Init[] {
	no this.receiverData
	this.senderData = Packet
	this.response = ACK
	no this.sentPacket
	no this.checkSum
	no this.tempSentPacket
}

pred State.End[] {
	no this.senderData and no this.sentPacket
	all p:Packet | p in this.receiverData
	this.response = ACK
}
run End for exactly 1 State, exactly 3 Packet

pred Step[s, s': State] {
	no s.checkSum => populateSentPacket[s, s'] else extractSentPacket[s, s']
}

pred populateSentPacket[s, s': State] {
	s.response = ACK => {
		one p : s.senderData | 
			s'.tempSentPacket = p and
			s'.sentPacket = p and
			s'.senderData = s.senderData - p and
			s'.receiverData = s.receiverData and
			one c: CheckSum | s'.checkSum = c
	}
	else {
		s'.sentPacket = s.tempSentPacket and
		s'.senderData = s.senderData and
		s'.receiverData = s.receiverData and
		one c: CheckSum | s'.checkSum = c
	}
}

pred extractSentPacket[s, s': State] {
	s.checkSum = Correct => {
		s'.receiverData = s.receiverData + s.sentPacket and
		no s'.sentPacket and
		s'.senderData = s.senderData and
		no s'.checkSum and
		no s'.tempSentPacket and
		s'.response = ACK
	}
	else {
		no s'.sentPacket and
		no s'.checkSum and
		s'.receiverData = s.receiverData and
		s'.senderData = s.senderData and
		s'.response = NAK
	}
}

pred Trace {
	first.Init
	all s: State - last |
		let s' = s.next |
			Step[s, s']
	last.End
}

run Trace for exactly 5 State, exactly 2 Packet
run Trace for exactly 7 State, exactly 2 Packet
run Init for exactly 1 State, exactly 5 Packet
