module project/m1
open util/ordering [State]

sig Packet {}

sig State {
	senderData: set Packet,
	receiverData: set Packet,
	sentPacket: lone Packet
} 
{
	senderData != receiverData
	some sentPacket => sentPacket not in senderData + receiverData
}

pred State.Init[] {
	no this.receiverData
	this.senderData = Packet
	no this.sentPacket
}

pred State.End[] {
	no this.senderData and no this.sentPacket
	all p:Packet | p in this.receiverData
}
run End for exactly 1 State, exactly 3 Packet

pred Step[s, s': State] {
	no s.sentPacket => populateSentPacket[s, s'] else extractSentPacket[s, s']
}

pred populateSentPacket[s, s': State] {
	one p : s.senderData | 
		s'.sentPacket = p and
		s'.senderData = s.senderData - p
}

pred extractSentPacket[s, s': State] {
	s'.receiverData = s.receiverData + s.sentPacket
	no s'.sentPacket
}

pred Trace {
	first.Init
	all s: State - last |
		let s' = s.next |
			Step[s, s']
	last.End
}

run Trace for exactly 5 State, exactly 2 Packet
run Init for exactly 1 State, exactly 5 Packet
