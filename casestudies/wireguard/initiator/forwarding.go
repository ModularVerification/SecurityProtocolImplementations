package initiator

//@ import arb "github.com/ModularVerification/ReusableVerificationLibrary/arbitrary"
//@ import ev "github.com/ModularVerification/ReusableVerificationLibrary/event"
//@ import "github.com/ModularVerification/ReusableVerificationLibrary/label"
//@ import labeledlib "github.com/ModularVerification/ReusableVerificationLibrary/labeledlibrary/library"
//@ import "github.com/ModularVerification/ReusableVerificationLibrary/labeling"
//@ import p "github.com/ModularVerification/ReusableVerificationLibrary/principal"
//@ import tm "github.com/ModularVerification/ReusableVerificationLibrary/term"
//@ import u "github.com/ModularVerification/ReusableVerificationLibrary/usage"
//@ import . "github.com/ModularVerification/casestudies/wireguard/verification/common"

import lib "github.com/ModularVerification/casestudies/wireguard/library"
//@ import .   "github.com/ModularVerification/casestudies/wireguard/verification/messages/initiator"
//@ import pap "github.com/ModularVerification/casestudies/wireguard/verification/pattern"


// trusted wrapper around the library's `GetPacket` function
// to express that the returned payload can only be sent to
// this actor's session or its peer but no one else. In particular, this
// stops an implementation of sending out the payload (i.e. a VPN packet)
// in plaintext to the network.
//@ trusted
//@ requires acc(InitiatorMem(initiator), 1/2)
//@ ensures  acc(InitiatorMem(initiator), 1/2)
//@ ensures  ok ==> labeledlib.Mem(res) && tm.gamma(term) == labeledlib.Abs(res)
//@ ensures  ok ==> GetWgLabeling().IsMsg(initiator.Snapshot(), term, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }))
func (initiator *Initiator) GetPacket() (res lib.ByteString, ok bool /*@, ghost term tm.Term @*/) {
	//@ unfold acc(InitiatorMem(initiator), 1/2)
	res, ok /*@, term @*/ = initiator.LibState.GetPacket()
	//@ fold acc(InitiatorMem(initiator), 1/2)
	return
}

//@ requires InitiatorMem(initiator) && lib.ConnectionMem(conn)
//@ requires lib.ConnectionSendKey(conn) == tm.gamma(kirT)
//@ requires lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
//@ requires initiator.transportKeysLabeling(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
//@ requires lib.ConnectionNonceVal(conn) == 0
func (initiator *Initiator) forwardPackets(conn *lib.Connection /*@, ghost ekiT tm.Term, ghost epkRX tm.Term, ghost ekRX tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost bSess uint32, ghost corrupted bool @*/) {

	//@ ghost var isFirstMessage bool = true
	//@ initiator.proveSecurityProperties(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)

	//@ invariant InitiatorMem(initiator) && lib.ConnectionMem(conn)
	//@ invariant lib.ConnectionSendKey(conn) == tm.gamma(kirT)
	//@ invariant lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
	//@ invariant initiator.transportKeysLabeling(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
	//@ invariant  isFirstMessage ==> lib.ConnectionNonceVal(conn) == 0
	//@ invariant !isFirstMessage ==> lib.ConnectionNonceVal(conn) > 0
	//@ invariant transportKeysStrongForwardSecrecy(initiator.Snapshot(), ekiT, epkRX, ekRX, kirT, kriT, initiator.getASessId(), initiator.getBSessId(bSess))
	//@ invariant initiator.InjectiveAgreementWithKCIResistance(initiator.getASessId(), initiator.getBSessId(bSess), sendFirstInitEv(ekiT, ekRX, kirT, kriT, initiator.getASessId(), initiator.getBSessId(bSess)), sendSidREv(tm.exp(tm.generator(), ekiT), ekRX, kirT, kriT, initiator.getASessId(), initiator.getBSessId(bSess)))
	for {
		//@ ghost rid := initiator.getRid()
		//@ ghost s0 := initiator.Snapshot()
		var request lib.ByteString
		var ok bool
		//@ ghost var term tm.Term
		request, ok /*@, term @*/ = initiator.GetPacket()
		
		if ok {
			//@ ghost var isInState3 bool
			ok /*@, isInState3 @*/ = initiator.sendMessage(request, conn /*@, isFirstMessage, ekiT, epkRX, ekRX, kirT, kriT, term, bSess, corrupted @*/)
			//@ isFirstMessage = !isInState3
			//@ initiator.transportKeysLabelingMonotonic(s0, ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)

			if ok {
				var response lib.ByteString
				var done bool = false // ADAPT
				//@ invariant InitiatorMem(initiator) && acc(lib.ConnectionMem(conn), 1/4)
				//@ invariant done ==> labeledlib.Mem(response)
				//@ invariant lib.ConnectionSendKey(conn) == tm.gamma(kirT)
				//@ invariant lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
				//@ invariant initiator.transportKeysLabeling(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
				for !done {
					response, done = initiator.receiveMessage(conn /*@, kirT, kriT @*/)
				}

				//@ unfold acc(InitiatorMem(initiator), 1/2)
				(initiator.LibState).ConsumePacket(response)
				//@ fold acc(InitiatorMem(initiator), 1/2)
			}
		}

		// with the following statement, we show that we can prove the specified
		// security properties after each iteration of the transport phase:
		//@ initiator.proveSecurityProperties(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
	}
}

//@ requires InitiatorMem(initiator) && lib.ConnectionMem(conn) && labeledlib.Mem(msg)
//@ requires labeledlib.Abs(msg) == tm.gamma(msgTerm)
//@ requires GetWgLabeling().IsMsg(initiator.Snapshot(), msgTerm, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }))
//@ requires lib.ConnectionSendKey(conn) == tm.gamma(kirT)
//@ requires lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
//@ requires initiator.transportKeysLabeling(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
//@ requires  isFirstMessage ==> lib.ConnectionNonceVal(conn) == 0
//@ requires !isFirstMessage ==> lib.ConnectionNonceVal(conn) > 0
//@ ensures  InitiatorMem(initiator) && lib.ConnectionMem(conn)
//@ ensures  initiator.ImmutableState() == old(initiator.ImmutableState())
//@ ensures  old(initiator.Snapshot()).isSuffix(initiator.Snapshot())
//@ ensures  lib.ConnectionSendKey(conn) == tm.gamma(kirT)
//@ ensures  lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
//@ ensures  !isFirstMessage ==> isInState3
//@ ensures  ok ==> isInState3
//@ ensures  !isInState3 ==> lib.ConnectionNonceVal(conn) == 0
//@ ensures  isInState3  ==> lib.ConnectionNonceVal(conn) > 0
func (initiator *Initiator) sendMessage(msg lib.ByteString, conn *lib.Connection /*@, ghost isFirstMessage bool, ghost ekiT tm.Term, ghost epkRX tm.Term, ghost ekRX tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost msgTerm tm.Term, ghost bSess uint32, ghost corrupted bool @*/) (ok bool /*@, ghost isInState3 bool @*/) {

	//@ ghost rid := initiator.getRid()
	//@ ghost pp := initiator.getPP()
	//@ isInState3 = !isFirstMessage
	//@ unfold lib.ConnectionMem(conn)

	if conn.Nonce >= 18446744073709543423 {
		//@ fold lib.ConnectionMem(conn)
		ok = false
		return
	}

	var nonce uint64
	if conn.Nonce == 0 {
		nonce = 0
	} else {
		nonce = lib.GetCounter(conn.Nonce)
	}
	nonceBytes := lib.NonceToBytes(nonce)

	//@ unfold acc(InitiatorMem(initiator), 1/8)
	plaintext := (initiator.LibState).PadMsg(msg)
	//@ fold acc(InitiatorMem(initiator), 1/8)

	//@ snapshot := initiator.Snapshot()
	//@ aId := initiator.getAId()
	//@ aSessId := initiator.getASessId()
	//@ bId := initiator.getBId()
	//@ bSessId := initiator.getBSessId(bSess)
	//@ a := aSessId.getPrincipal()
	//@ b := bSessId.getPrincipal()
	//@ aSessBId := label.Readers(set[p.Id]{ aSessId, bId })
	// the following assert stmt is necessary:
	//@ assert GetWgLabeling().IsAeadKey(snapshot, kirT, aSessBId, WgSendingKey)
	//@ dhStatic := GetWgUsage().getDhStaticFromKir(kirT)
	// note that the next assert stmt is needed because `payloadToResponderPred` is triggered on `p.principalId(a)` and `p.principalId(b)`:
	//@ assert GetWgLabeling().GetLabel(dhStatic) == label.Join(label.Readers(set[p.Id]{ p.principalId(a) }), label.Readers(set[p.Id]{ p.principalId(b) }))
	//@ prefix := getHandshakeDonePrefix(snapshot, ekiT, epkRX, ekRX, kirT, kriT, aSessId, bSessId)
	/*@
	ghost if corrupted {
		GetWgLabeling().IsPublishableMonotonic(prefix, snapshot, kirT)
	}
	@*/
	//@ assert GetWgUsage().AeadPred(snapshot, WgSendingKey, kirT, tm.integer64(nonce), msgTerm, tm.zeroString(0))
	//@ unfold InitiatorMem(initiator)
	encryptedMsg, err := initiator.llib.AeadEnc(conn.SendKey, nonceBytes, plaintext, nil /*@, kirT, tm.integer64(nonce), msgTerm, tm.zeroString(0), aSessBId @*/)
	ok = err == nil
	//@ fold InitiatorMem(initiator)
	if !ok {
		//@ fold lib.ConnectionMem(conn)
		return
	}

	message := &lib.Message{
		Type:     4,
		Receiver: conn.RemoteIndex,
		Nonce:    nonce,
		Payload:  encryptedMsg,
	}
	//@ sidR := tm.integer32B(conn.RemoteIndex)
	//@ sidrT := tm.integer32(conn.RemoteIndex)

	//@ fold lib.ConnectionMem(conn)

	packet := lib.MarshalMessage(message)

	//@ packetT := tm.tuple4(tm.integer32(4), sidrT, tm.integer64(nonce), tm.aead(kirT, tm.integer64(nonce), msgTerm, tm.zeroString(0)))
	//@ assert labeledlib.Abs(packet) == tm.gamma(packetT)

	//@ isInState3 = true

	//@ unfold lib.ConnectionMem(conn)
	conn.Nonce += 1
	//@ fold lib.ConnectionMem(conn)

	// the following assert stmts are necessary:
	//@ assert GetWgLabeling().IsValid(initiator.Snapshot(), tm.integer64(nonce))
	//@ assert GetWgLabeling().IsValid(initiator.Snapshot(), msgTerm)
	//@ assert GetWgLabeling().IsValid(initiator.Snapshot(), tm.zeroString(0))
	//@ assert GetWgLabeling().IsValidAead(initiator.Snapshot(), kirT, tm.integer64(nonce), msgTerm, GetWgLabeling().GetLabel(msgTerm), tm.zeroString(0))
	//@ GetWgLabeling().IsMsgTupleCreate(initiator.Snapshot(), packetT, label.Public())

	//@ unfold InitiatorMem(initiator)
	err = initiator.llib.Send(lib.Principal(initiator.a), lib.Principal(initiator.b), packet /*@, packetT @*/)
	ok = err == nil
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold InitiatorMem(initiator)

	return
}

//@ requires InitiatorMem(initiator) && acc(lib.ConnectionMem(conn), 1/8)
//@ requires lib.ConnectionSendKey(conn) == tm.gamma(kirT)
//@ requires lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
//@ requires GetWgLabeling().IsSecretRelaxed(initiator.Snapshot(), kirT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), u.AeadKey(WgSendingKey))
//@ requires GetWgLabeling().IsSecretRelaxed(initiator.Snapshot(), kriT, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), u.AeadKey(WgReceivingKey))
//@ ensures  InitiatorMem(initiator) && acc(lib.ConnectionMem(conn), 1/8)
//@ ensures  initiator.ImmutableState() == old(initiator.ImmutableState())
//@ ensures  old(initiator.Snapshot()) == initiator.Snapshot()
//@ ensures  ok ==> labeledlib.Mem(msg)
func (initiator *Initiator) receiveMessage(conn *lib.Connection /*@, ghost kirT tm.Term, ghost kriT tm.Term @*/) (msg lib.ByteString, ok bool) {

	//@ ghost rid := initiator.getRid()
	//@ unfold acc(InitiatorMem(initiator), 1/8)
	packet, err /*@, term @*/ := initiator.LibState.Receive(lib.Principal(initiator.b), lib.Principal(initiator.a) /*@, initiator.llib.Snapshot() @*/ )
	ok = err == nil
	//@ fold acc(InitiatorMem(initiator), 1/8)
	if !ok {
		return
	}
	//@ recvB := labeledlib.Abs(packet)

	message, ok := lib.UnmarshalMessage(packet)
	if !ok {
		return
	}

	ok = message.Type == 4
	if !ok {
		return
	}

	//@ unfold acc(InitiatorMem(initiator), 1/8)
	//@ unfold acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/8)
	ok = (initiator.HandshakeInfo).LocalIndex == message.Receiver
	//@ fold acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/8)
	//@ fold acc(InitiatorMem(initiator), 1/8)
	if !ok {
		return
	}

	nonceBytes := lib.NonceToBytes(message.Nonce)

	//@ snapshot := initiator.Snapshot()
	//@ aSessId := initiator.getASessId()
	//@ bId := initiator.getBId()
	//@ bothL := label.Readers(set[p.Id]{ aSessId, bId })
	/*@
	predictedPayloadT := tm.oneTerm(labeledlib.Abs(message.Payload))
	ghost if term.IsTuple4() {
		predictedPayloadT = tm.getTupleElem(term, 3)
	}
	@*/
	//@ unfold acc(lib.ConnectionMem(conn), 1/8)
	//@ unfold InitiatorMem(initiator)
	plaintext, err := initiator.llib.AeadDec(conn.RecvKey, nonceBytes, message.Payload, nil /*@, kriT, tm.integer64(message.Nonce), predictedPayloadT, tm.zeroString(0), bothL @*/)
	//@ fold InitiatorMem(initiator)
	ok = err == nil
	//@ fold acc(lib.ConnectionMem(conn), 1/8)
	if !ok { // ADAPT
		return
	}

	/*@
	pp := initiator.getPP()
	recvB := labeledlib.Abs(packet)
	sidI := tm.integer32B(message.Receiver)
	nonceB := tm.integer64B(message.Nonce)
	assert recvB == tm.gamma(tm.tuple4(tm.oneTerm(tm.integer32B(4)), rid, tm.oneTerm(nonceB), tm.aead(kriT, tm.oneTerm(nonceB), tm.oneTerm(labeledlib.Abs(plaintext)), tm.zeroString(0))))

	unfold acc(InitiatorMem(initiator), 1/4)
	fold pap.pattern4Constraints(initiator.llib, bId, WgReceivingKey, rid, kriT)
	nRI, p := pap.patternProperty4(initiator.llib, bId, WgReceivingKey, rid, kriT, tm.oneTerm(nonceB), tm.oneTerm(labeledlib.Abs(plaintext)), term)
	unfold pap.pattern4Constraints(initiator.llib, bId, WgReceivingKey, rid, kriT)
	fold acc(InitiatorMem(initiator), 1/4)
	assert term == tm.tuple4(tm.integer32(4), rid, nRI, tm.aead(kriT, nRI, p, tm.zeroString(0)))
	@*/

	msg = lib.CombineMsg(message.Type, message.Receiver, message.Nonce, plaintext)

	return
}
