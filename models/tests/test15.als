module tests/test // Bugpost by Marijn Koesen

abstract sig sexualPreference {}

one sig Bisexual, Gay, Straight extends sexualPreference {}

abstract sig Person {
        sexualPreference : one sexualPreference,
        date : set Person
}

abstract sig Male,Female extends Person {}

one sig Karel, Klaas, Peter extends Male {}
one sig Karolien, Petra, Floor extends Female {}

fact Mensen {
        Karel.sexualPreference = Gay
        Klaas.sexualPreference = Straight
        Peter.sexualPreference = Bisexual
        Karolien.sexualPreference = Gay
        Petra.sexualPreference = Bisexual
        Floor.sexualPreference = Straight
}

run {} expect 1
