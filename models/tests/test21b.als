module tests/test21b // Bugpost by nicolas.rouquette@jpl.nasa.gov

open tests/test21a as part1

sig CL extends T2 {}
sig C extends CL {
   s : one SM
}

sig SM extends T2 {}
{
    t = this.~@s
    t = this.~@s
    this.@t = this.~@s
    this.@t = this.~@s
    this.@t = this.~@s
    this.@t = this.~@s
}

run { } expect 1
