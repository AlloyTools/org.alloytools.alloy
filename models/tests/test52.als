module tests/test52 -- example created by Daniel Jackson

sig Peg {}
sig Red, Green, Blue, Yellow, White, Black extends Peg {}

abstract sig Pin {}
sig BlackPin, WhitePin extends Pin {}

sig Round {}

sig Game {
        solution: set Peg,
        guess: solution -> one Peg -> Round
        } {
        all r: Round {
                no Peg.guess.r & guess.Peg.r
                #solution.r = 4 // This line should give a "cannot perform relational join" error
                #(solution.r).(guess.r) = 4
        }
}

pred nodups (s: seq univ) {
        no disj i, j: Int | i.s = j.s and some i.s
        }

run {some Game} for 8 but 1 Game
