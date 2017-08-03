module tests/test // Bugpost by Marijn Koesen

abstract sig sexualPreference {}

one sig Bisexual, Gay, Straight extends sexualPreference {}

abstract sig Person {
        SexualPreference : one sexualPreference
}

run {} expect 1
