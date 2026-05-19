#@exec Read("MinimalIntersections.g");
#@local m1, m2, m3, m4, m5, m6, m7, m8, m9, is_si1, is_si2, is_si3, is_si4, is_si5, is_si6, is_si7, is_si8, is_si9, cp1, cp2, cp3, cp4, cp5, cp6, cp7, cp8, cp9
gap> START_TEST("MinimalIntersections.tst");

## Case 1: No self-inverse classes at i >= 2 — nothing touched by either function.
gap> is_si1 := [true, false, false, false];;
gap> m1 := rec(cl_ints := [0, 2, 3, 6], vals := [1, 3, 5, 7]);;
gap> m1.moduli := m1.vals;;
gap> IsParityValidMin(m1, is_si1);
true
gap> ModularParityAdjust(is_si1, m1);;
gap> m1.vals;
[ 1, 3, 5, 7 ]
gap> m1.cl_ints;
[ 0, 2, 3, 6 ]
gap> IsParityValidMin(m1, is_si1);
true
gap> cp1 := StructuralCopy(m1);;
gap> ModularParityAdjust(is_si1, m1);;
gap> m1 = cp1;
true

## Case 2: Self-inverse at i=2, vals odd, cl_ints even — vals doubles, cl_ints unchanged.
gap> is_si2 := [true, true, false, false];;
gap> m2 := rec(cl_ints := [0, 4, 3, 6], vals := [1, 3, 5, 7]);;
gap> m2.moduli := m2.vals;;
gap> IsParityValidMin(m2, is_si2);
true
gap> ModularParityAdjust(is_si2, m2);;
gap> m2.vals;
[ 1, 6, 5, 7 ]
gap> m2.cl_ints;
[ 0, 4, 3, 6 ]
gap> IsParityValidMin(m2, is_si2);
true
gap> cp2 := StructuralCopy(m2);;
gap> ModularParityAdjust(is_si2, m2);;
gap> m2 = cp2;
true

## Case 3: Self-inverse at i=2, vals odd, cl_ints odd — cl_ints bumped to 8, vals doubles.
gap> is_si3 := [true, true, false, false];;
gap> m3 := rec(cl_ints := [0, 5, 3, 6], vals := [1, 3, 5, 7]);;
gap> m3.moduli := m3.vals;;
gap> IsParityValidMin(m3, is_si3);
true
gap> ModularParityAdjust(is_si3, m3);;
gap> m3.vals;
[ 1, 6, 5, 7 ]
gap> m3.cl_ints;
[ 0, 8, 3, 6 ]
gap> IsParityValidMin(m3, is_si3);
true
gap> cp3 := StructuralCopy(m3);;
gap> ModularParityAdjust(is_si3, m3);;
gap> m3 = cp3;
true

## Case 4: Self-inverse at i=2, vals even, cl_ints odd — ModularParityAdjust leaves it alone,
##          IsParityValidMin rejects it. Regression test for the even-modulus parity bug.
gap> is_si4 := [true, true, false, false];;
gap> m4 := rec(cl_ints := [0, 3, 3, 6], vals := [1, 4, 5, 7]);;
gap> m4.moduli := m4.vals;;
gap> IsParityValidMin(m4, is_si4);
false
gap> ModularParityAdjust(is_si4, m4);;
gap> m4.vals;
[ 1, 4, 5, 7 ]
gap> m4.cl_ints;
[ 0, 3, 3, 6 ]
gap> IsParityValidMin(m4, is_si4);
false
gap> cp4 := StructuralCopy(m4);;
gap> ModularParityAdjust(is_si4, m4);;
gap> m4 = cp4;
true

## Case 5: Mixed — i=3 self-inverse triggers bump, i=4 self-inverse skipped (vals even),
##          i=2 non-self-inverse skipped entirely.
gap> is_si5 := [true, false, true, true];;
gap> m5 := rec(cl_ints := [0, 2, 3, 6], vals := [1, 3, 5, 4]);;
gap> m5.moduli := m5.vals;;
gap> IsParityValidMin(m5, is_si5);
true
gap> ModularParityAdjust(is_si5, m5);;
gap> m5.vals;
[ 1, 3, 10, 4 ]
gap> m5.cl_ints;
[ 0, 2, 8, 6 ]
gap> IsParityValidMin(m5, is_si5);
true
gap> cp5 := StructuralCopy(m5);;
gap> ModularParityAdjust(is_si5, m5);;
gap> m5 = cp5;
true

## Case 6: Multi-bump, all even cl_ints — both self-inverse positions get vals doubled only.
gap> is_si6 := [true, true, true, false];;
gap> m6 := rec(cl_ints := [0, 4, 6, 2], vals := [1, 3, 5, 7]);;
gap> m6.moduli := m6.vals;;
gap> IsParityValidMin(m6, is_si6);
true
gap> ModularParityAdjust(is_si6, m6);;
gap> m6.vals;
[ 1, 6, 10, 7 ]
gap> m6.cl_ints;
[ 0, 4, 6, 2 ]
gap> IsParityValidMin(m6, is_si6);
true
gap> cp6 := StructuralCopy(m6);;
gap> ModularParityAdjust(is_si6, m6);;
gap> m6 = cp6;
true

## Case 7: Multi-bump, all odd cl_ints — both self-inverse positions get cl_ints bumped and vals doubled.
gap> is_si7 := [true, true, true, false];;
gap> m7 := rec(cl_ints := [0, 5, 7, 2], vals := [1, 3, 5, 7]);;
gap> m7.moduli := m7.vals;;
gap> IsParityValidMin(m7, is_si7);
true
gap> ModularParityAdjust(is_si7, m7);;
gap> m7.vals;
[ 1, 6, 10, 7 ]
gap> m7.cl_ints;
[ 0, 8, 12, 2 ]
gap> IsParityValidMin(m7, is_si7);
true
gap> cp7 := StructuralCopy(m7);;
gap> ModularParityAdjust(is_si7, m7);;
gap> m7 = cp7;
true

## Case 8: Mixed bump — i=2 has even cl_ints (vals only doubles), i=3 has odd cl_ints (bump + double).
gap> is_si8 := [true, true, true, false];;
gap> m8 := rec(cl_ints := [0, 4, 7, 2], vals := [1, 3, 5, 7]);;
gap> m8.moduli := m8.vals;;
gap> IsParityValidMin(m8, is_si8);
true
gap> ModularParityAdjust(is_si8, m8);;
gap> m8.vals;
[ 1, 6, 10, 7 ]
gap> m8.cl_ints;
[ 0, 4, 12, 2 ]
gap> IsParityValidMin(m8, is_si8);
true
gap> cp8 := StructuralCopy(m8);;
gap> ModularParityAdjust(is_si8, m8);;
gap> m8 = cp8;
true

## Case 9: is_si=true, vals even, cl_ints even — no mutation, passes filter.
gap> is_si9 := [true, true, false, false];;
gap> m9 := rec(cl_ints := [0, 6, 3, 2], vals := [1, 4, 5, 7]);;
gap> m9.moduli := m9.vals;;
gap> IsParityValidMin(m9, is_si9);
true
gap> ModularParityAdjust(is_si9, m9);;
gap> m9.vals;
[ 1, 4, 5, 7 ]
gap> m9.cl_ints;
[ 0, 6, 3, 2 ]
gap> IsParityValidMin(m9, is_si9);
true
gap> cp9 := StructuralCopy(m9);;
gap> ModularParityAdjust(is_si9, m9);;
gap> m9 = cp9;
true
gap> STOP_TEST("MinimalIntersections.tst");
