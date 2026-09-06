# =====================================================================
# Case coverage matrix: 5 operators x 4 type pairings.
# Distinct operands, so every operator gets a definite answer.
# =====================================================================
1
check:
(
    # int * int  (case 2.2)
    (3 < 4 ) ,
    (3 <= 4)  ,
    !(3 > 4 ) ,
    !(3 >= 4)  ,
    !(3 == 4)  ,
    !(4 < 3 ) ,
    !(4 <= 3)  ,
    (4 > 3 ) ,
    (4 >= 3)  ,
    !(4 == 3) ) 
    spits (true, true, true, true, true, true, true, true, true, true)
end

check:
(
    # float * float  (case 1.1)
    (3.0 < 4.0) ,
    (3.0 <= 4.0) ,
    !(3.0 > 4.0) ,
    !(3.0 >= 4.0) ,
    !(3.0 == 4.0) ,

    !(4.0 < 3.0) ,
    !(4.0 <= 3.0) ,
    (4.0 > 3.0) ,
    (4.0 >= 3.0) ,
    !(4.0 == 3.0) )
    spits (true, true, true, true, true, true, true, true, true, true)
end

check:
(
    # int * float  (case 2.1)
    (3 < 4.0) ,
    (3 <= 4.0) ,
    !(3 > 4.0) ,
    !(3 >= 4.0) ,
    !(3 == 4.0) ,

    !(4 < 3.0) ,
    !(4 <= 3.0) ,
    (4 > 3.0) ,
    (4 >= 3.0) ,
    !(4 == 3.0) )
    spits (true, true, true, true, true, true, true, true, true, true)
end

check:
(
    # float * int  (case 1.2)
    (3.0 < 4) ,
    (3.0 <= 4) ,
    !(3.0 > 4) ,
    !(3.0 >= 4) ,
    !(3.0 == 4) ,

    !(4.0 < 3) ,
    !(4.0 <= 3) ,
    (4.0 > 3) ,
    (4.0 >= 3) ,
    !(4.0 == 3) )
    spits (true, true, true, true, true, true, true, true, true, true)
end

# =====================================================================
# Equal operands. These separate < from <=, > from >=, and confirm
# that == holds across every type pairing.
# =====================================================================

check:
(
    !(3 < 3) ,
    (3 <= 3) ,
    !(3 > 3) ,
    (3 >= 3) ,
    (3 == 3) ,

    !(3.0 < 3.0) ,
    (3.0 <= 3.0) ,
    !(3.0 > 3.0) ,
    (3.0 >= 3.0) ,
    (3.0 == 3.0) )
    spits (true, true, true, true, true, true, true, true, true, true)
end

check:
(
  # Same value, mixed representations. The int is promoted for the
  # ordering operators and the float is  truncated for ==; both must
  # agree that the values are equal.
    !(3 < 3.0) ,
    (3 <= 3.0) ,
    !(3 > 3.0) ,
    (3 >= 3.0) ,
    (3 == 3.0) ,

    !(3.0 < 3) ,
    (3.0 <= 3) ,
    !(3.0 > 3) ,
    (3.0 >= 3) ,
    (3.0 == 3) )
    spits (true, true, true, true, true, true, true, true, true, true)
end

# =====================================================================
# Fractional values against ints. These are the regression tests for
# promoting rather than truncating in the ordering operators: under
# truncation 3.5 and 3 would compare equal.
# =====================================================================

check:
(
    (3.5 > 3) ,
    (3.5 >= 3) ,
    !(3.5 < 3) ,
    !(3.5 <= 3) ,
    !(3.5 == 3) ,

    (3 < 3.5) ,
    (3 <= 3.5) ,
    !(3 > 3.5) ,
    !(3 >= 3.5) ,
    !(3 == 3.5) )
    spits (true, true, true, true, true, true, true, true, true, true)
end

check:
(
    (3.5 < 4) ,
    (3.5 <= 4) ,
    !(3.5 > 4) ,
    !(3.5 >= 4) ,
    !(3.5 == 4) ,

    (4 > 3.5) ,
    (4 >= 3.5) ,
    !(4 < 3.5) ,
    !(4 <= 3.5) ,
    !(4 == 3.5) )
    spits (true, true, true, true, true, true, true, true, true, true)
end

# =====================================================================
# Negative values. The int path uses the signed jump family and the
# float path uses the unsigned one; both must order negatives correctly.
# Truncation toward zero also behaves asymmetrically around zero, so
# each fractional case is repeated with a negative operand.
# =====================================================================

check:
(
    (-5 < 3) ,
    (-5 <= 3) ,
    !(-5 > 3) ,
    !(-5 >= 3) ,
    !(-5 == 3) ,

    (-5 < -3) ,
    !(-5 > -3) ,
    !(-3 < -5) ,
    (-3 > -5) ,
    (-5 == -5) )
    spits (true, true, true, true, true, true, true, true, true, true)
end

check:
(
    (-5.0 < 3.0) ,
    !(-5.0 > 3.0) ,
    (-5.0 < -3.0) ,
    !(-5.0 > -3.0) ,
    (-5.0 == -5.0) ,

    (-5.0 < 3) ,
    (-5 < 3.0) ,
    (-5.0 == -5) ,
    (-5 == -5.0) )
    spits (true, true, true, true, true, true, true, true, true)
end

check:
(
  # -3.5 truncates toward zero to -3, so a truncating == would
  # wrongly report equality here.
    !(-3.5 == -3) ,
    !(-3 == -3.5) ,
    (-3.5 < -3) ,
    (-3.5 <= -3) ,
    !(-3.5 > -3) ,
    (-3.5 > -4) ,
    !(-3.5 == -4) ,
    (-4 < -3.5) ) 
    spits (true, true, true, true, true, true, true, true)
end

# =====================================================================
# Zero, including negative zero. IEEE says -0.0 and 0.0 compare equal,
# and comisd reports them equal, so every pairing below is an equality.
# =====================================================================

check:
(
    (0 == 0) ,
    (0.0 == 0.0) ,
    (0.0 == 0) ,
    (0 == 0.0) ,
    (-0.0 == 0.0) ,
    (-0.0 == 0) ,
    (0 == -0.0) ,
    (-0.0 == 0.0) )
    spits (true, true, true, true, true, true, true, true)
end

check:
(
    !(0.0 < -0.0) ,
    (0.0 <= -0.0) ,
    !(0.0 > -0.0) ,
    (0.0 >= -0.0) ,
    !(-0.0 < 0) ,
    (-0.0 <= 0) ,

    (0 < 0.5) ,
    (-0.5 < 0) ,
    !(-0.5 == 0) ,
    !(0.5 == 0) )
    spits (true, true, true, true, true, true, true, true, true, true)
end

check:
(
  # Ordinary large-but-exact values, in both operand orders.
    (1000000000000.0 == 1000000000000) ,
    (1000000000000 == 1000000000000.0) ,
    !(1000000000000.5 == 1000000000000) ,
    (1000000000000.5 > 1000000000000) ,
    (999999999999.0 < 1000000000000) )
    spits (true, true, true, true, true)
end