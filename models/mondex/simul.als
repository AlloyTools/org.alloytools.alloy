module mondex/simul
open mondex/common as mondexCOMMON
open mondex/a as mondexA
open mondex/b as mondexB
open mondex/c as mondexC
open mondex/cw as mondexCW
open mondex/bop as mondexBOP
open mondex/rab as mondexRAB

pred trans (a, a' : AbWorld, b0, b1, b2, b3, b4, b5 : ConWorld,
in1, in2, in3, in4, in5, out1, out2, out3, out4, out5 : MESSAGE,
pfrom, pto : ConPurse, a_in : AIN, a_out  : AOUT) {
    RabCl2 [a, b0]
    RabCl [a', b5, chosenLost [a, b0]]
    Abstract [a]
    Between [b0]
    StartFromEafrom [b0, b1, pfrom, in1, out1]
    StartToEafrom [b1, b2, pto, in2, out2]
    ReqOkay [b2, b3, pfrom, in3, out3]
    ValOkay [b3, b4, pto, in4, out4]
    AckOkay [b4, b5, pfrom, in5, out5]
    AbTransferOkay [a, a', a_in, a_out]
    some in1.value
    some pfrom.balance.b5
    some pto.balance.b0
}

run trans for 2 AbWorld, 6 ConState, 10 MESSAGE, 2 Purse, 1 TransferDetails, 1 AOUT, 3 Coin, 12 SEQNO
