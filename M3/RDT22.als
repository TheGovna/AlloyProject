module project/m22
open util/ordering [State]

abstract sig Response {
	seqNum: one SequenceNumber
}
abstract sig ACK extends Response {}
abstract sig ACKCorrupt extends Response {}
one sig ACKOne, ACKZero extends ACK{
}
one sig ACKZeroCorrupt, ACKOneCorrupt extends ACKCorrupt{
}

abstract sig CheckSum {}
one sig Correct, Error extends CheckSum {}

abstract sig SequenceNumber {}
one sig Zero, One extends SequenceNumber {}

sig Packet {
	seqNum: one SequenceNumber
}

sig State {
	senderData: set Packet,
	receiverData: set Packet,
	sentPacket: lone Packet,
	tempSentPacket: lone Packet,  // version of packet that sender saves to resend if necessary
	checkSum: lone CheckSum,
	response: lone Response
} 

pred State.Init[] {
	no this.receiverData
	this.senderData = Packet
	this.response = ACKOne
	no this.sentPacket
	no this.checkSum
	no this.tempSentPacket
}

pred State.End[] {
	no this.senderData and no this.sentPacket
	Packet = this.receiverData
	(this.response = ACKOne or this.response = ACKZero)
}

pred Step[s, s': State] {
	(not Packet = s.receiverData and not s.response = ACK) => (
		no s.checkSum => 
			populateSentPacket[s, s']
		else 
			extractSentPacket[s, s'])
	else (
		s'.senderData = s.senderData and
		s'.receiverData = s.receiverData and
		s'.sentPacket = s.sentPacket and
		s'.tempSentPacket = s.tempSentPacket and
		s'.checkSum = s.checkSum and
		s'.response = s.response 
	)
}

pred populateSentPacket[s, s': State] {
	no s.tempSentPacket =>
		sendNextPacket[s,s']
	else
		((s.response = ACKOne or s.response = ACKZero) => 
			(s.response.seqNum = s.tempSentPacket.seqNum => 
				sendNextPacket[s,s']
			else
				resendPacket[s,s'])
		else
			resendPacket[s,s'])
}


pred sendNextPacket[s,s': State] {
	one p : s.senderData | 
		s'.sentPacket.seqNum = nextSequence[s.tempSentPacket.seqNum] and
		s'.tempSentPacket = p and
		s'.sentPacket = p and
		s'.senderData = s.senderData - p and
		s'.receiverData = s.receiverData and
		no s'.response and
		one c: CheckSum | s'.checkSum = c
}

pred TestSendNextPacket[] {
	first.Init
	sendNextPacket[first, first.next]
}

run TestSendNextPacket for exactly 2 State, exactly 1 Packet 


fun nextSequence[s:SequenceNumber] : SequenceNumber {
	s = Zero => 
		One
	else
		Zero
}

pred resendPacket[s, s': State] {
	s'.sentPacket = s.tempSentPacket and
	s'.tempSentPacket = s.tempSentPacket and
	s'.senderData = s.senderData and
	s'.receiverData = s.receiverData and
	no s'.response and
	one c: CheckSum | s'.checkSum = c
}

pred TestResendPacket[] {
	first.Init
	sendNextPacket[first,first.next]
	first.next.checkSum = Error
	incorrectChecksum[first.next, first.next.next]
	resendPacket[first.next.next, first.next.next.next]
}

run TestResendPacket for exactly 4 State, exactly 2 Packet 

pred extractSentPacket[s, s': State] {
	s.checkSum = Correct =>
		correctChecksum[s,s']
	else
		incorrectChecksum[s,s']
}

pred correctChecksum[s,s': State] {
	s'.receiverData = s.receiverData + s.sentPacket and
	no s'.sentPacket and
	s'.senderData = s.senderData and
	s'.tempSentPacket = s.tempSentPacket and
	no s'.checkSum and
	s'.response.seqNum = s.tempSentPacket.seqNum and
	(s'.response.seqNum = Zero => 
		(s'.response = ACKZero or
		s'.response = ACKZeroCorrupt)
	else 
	(s'.response = ACKOne or
	s'.response = ACKOneCorrupt))
}

pred TestCorrectChecksum[] {
	first.Init
	sendNextPacket[first,first.next]
	first.next.checkSum = Correct
	correctChecksum[first.next, first.next.next]
}

run TestCorrectChecksum for exactly 3 State, exactly 1 Packet 

pred incorrectChecksum[s,s':State] {
	no s'.sentPacket and
	s'.tempSentPacket = s.tempSentPacket and
	no s'.checkSum and
	s'.receiverData = s.receiverData and
	s'.response.seqNum = nextSequence[s.tempSentPacket.seqNum] and
	s'.senderData = s.senderData and
	(s'.response.seqNum = Zero => (s'.response = ACKZero or
	s'.response = ACKZeroCorrupt)
	else (
	s'.response = ACKOne or
	s'.response = ACKOneCorrupt))
}

pred TestIncorrectChecksum[] {
	first.Init
	sendNextPacket[first,first.next]
	first.next.checkSum = Error
	incorrectChecksum[first.next, first.next.next]
}

run TestIncorrectChecksum for exactly 3 State, exactly 1 Packet 

pred testFullCycle[] {
	first.Init
	sendNextPacket[first,first.next]
	first.next.checkSum = Correct
	correctChecksum[first.next, first.next.next]
	sendNextPacket[first.next.next,first.next.next.next]

	first.next.next.next.checkSum = Error
	incorrectChecksum[first.next.next.next, first.next.next.next.next]
}

run testFullCycle for exactly 5 State, exactly 2 Packet

pred Trace {
	first.Init
	all s: State - last |
		let s' = s.next |
			Step[s, s']
	last.End
}

pred testStep[] {
	first.Init
	Step[first, first.next]
	//Step[first.next, first.next.next]
}

run testStep for exactly 2 State, exactly 1 Packet
run Trace for exactly 3 State, exactly 1 Packet
run Trace for exactly 5 State, exactly 2 Packet
run Trace for exactly 7 State, exactly 2 Packet
run Init for exactly 1 State, exactly 1 Packet
run End for exactly 1 State, exactly 1 Packet
