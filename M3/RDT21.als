module project/m21
open util/ordering [State]

abstract sig Response {}
one sig ACK, NAK, ACKCorrupt, NAKCorrupt extends Response {}

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
{
	no p :Packet | p in senderData and p in receiverData
	all p: Packet | p in senderData or p in receiverData or p = tempSentPacket
}

fact sequenceFollowed {
	#(Packet - {p:Packet | p.seqNum = Zero}) = #(Packet - {p:Packet | p.seqNum = One}) or
	#(Packet - {p:Packet | p.seqNum = Zero}) = #(Packet - {p:Packet | p.seqNum = One}) + 1
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

pred Step[s, s': State] {
	no s.checkSum => populateSentPacket[s, s'] else extractSentPacket[s, s']
}

pred populateSentPacket[s, s': State] {
	s.response = ACK => 
		sendNextPacket[s,s']
	else
		resendCorruptAck[s,s']
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

run TestSendNextPacket for exactly 2 State, exactly 2 Packet 


fun nextSequence[s:SequenceNumber] : SequenceNumber {
	s = Zero => 
		One
	else
		Zero
}

pred resendCorruptAck[s, s': State] {
	s'.sentPacket = s.tempSentPacket and
	s'.tempSentPacket = s.tempSentPacket and
	s'.senderData = s.senderData and
	s'.receiverData = s.receiverData and
	one c: CheckSum | s'.checkSum = c
}

pred TestresendCorruptAck[] {
	first.Init
	sendNextPacket[first,first.next]
	incorrectChecksum[first.next, first.next.next]
	resendCorruptAck[first.next.next, first.next.next.next]
}

run TestresendCorruptAck for exactly 4 State, exactly 2 Packet 

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
	(s'.response = ACK or
	s'.response = ACKCorrupt)
}

pred TestCorrectChecksum[] {
	first.Init
	sendNextPacket[first,first.next]
	correctChecksum[first.next, first.next.next]
}

run TestCorrectChecksum for exactly 3 State, exactly 2 Packet 

pred incorrectChecksum[s,s':State] {
	no s'.sentPacket and
	s'.tempSentPacket = s.tempSentPacket and
	no s'.checkSum and
	s'.receiverData = s.receiverData and
	s'.senderData = s.senderData and
	(s'.response = NAK or
	s'.response = NAKCorrupt)
}

pred TestIncorrectChecksum[] {
	first.Init
	sendNextPacket[first,first.next]
	incorrectChecksum[first.next, first.next.next]
}

run TestIncorrectChecksum for exactly 3 State, exactly 2 Packet 

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
run End for exactly 1 State, exactly 3 Packet
