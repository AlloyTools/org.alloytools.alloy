module tests/test // Bugpost by Marijn Koesen

abstract sig sexualPreference {}

one sig Bisexual, Gay, Straight extends sexualPreference {}

abstract sig Person {
        sexualPreference : one sexualPreference
}

run {} expect 1
