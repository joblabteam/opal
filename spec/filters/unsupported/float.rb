opal_unsupported_filter "Float" do
  fails "BasicObject#__id__ returns a different value for two Float literals"
  fails "Complex#/ with Fixnum raises a ZeroDivisionError when given zero"
  fails "Complex#eql? returns false when the imaginary parts are of different classes"
  fails "Complex#eql? returns false when the real parts are of different classes"
  fails "Complex#quo with Fixnum raises a ZeroDivisionError when given zero"
  fails "Complex#rationalize raises RangeError if self has 0.0 imaginary part"
  fails "Complex#to_f when the imaginary part is Float 0.0 raises RangeError"
  fails "Complex#to_i when the imaginary part is Float 0.0 raises RangeError"
  fails "Complex#to_r when the imaginary part is Float 0.0 raises RangeError"
  fails "Complex#to_s returns 1+0.0i for Complex(1, 0.0)"
  fails "Complex#to_s returns 1-0.0i for Complex(1, -0.0)"
  fails "Fixnum#% raises a ZeroDivisionError when the given argument is 0 and a Float"
  fails "Fixnum#% raises a ZeroDivisionError when the given argument is 0"
  fails "Fixnum#& raises a TypeError when passed a Float"
  fails "Fixnum#/ raises a ZeroDivisionError if the given argument is zero and not a Float"
  fails "Fixnum#/ returns self divided by the given argument"
  fails "Fixnum#/ supports dividing negative numbers"
  fails "Fixnum#coerce when given a String returns  an array containing two Floats"
  fails "Fixnum#div coerces self and the given argument to Floats and returns self divided by other as Fixnum"
  fails "Fixnum#divmod raises a TypeError when given a non-Integer"
  fails "Fixnum#^ raises a TypeError when passed a Float"
  fails "Fixnum#| raises a TypeError when passed a Float"
  fails "Float constant MAX_10_EXP is 308"
  fails "Float constant MAX_EXP is 1024"
  fails "Float constant MIN is 2.2250738585072e-308"
  fails "Float constant MIN_10_EXP is -308"
  fails "Float constant MIN_EXP is -1021"
  fails "Float#coerce returns [other, self] both as Floats"
  fails "Float#eql? returns false if other is not a Float"
  fails "Float#to_s emits '-' for -0.0"
  fails "Float#to_s emits a trailing '.0' for a whole number"
  fails "Float#to_s emits a trailing '.0' for the mantissa in e format"
  fails "Float#to_s returns '0.0' for 0.0"
  fails "Marshal.dump Float -Infinity returns a binary string" # TypeError: can't bind singleton method to a different class (expected -Infinity.kind_of?(Float to be true)
  fails "Marshal.dump Float Infinity returns a binary string" # TypeError: can't bind singleton method to a different class (expected Infinity.kind_of?(Float to be true)
  fails "Math.gamma returns approximately (n-1)! given n for n between 24 and 30" # precision error
  fails "Rational#% returns a Float value when the argument is Float"
  fails "Rational#** raises ZeroDivisionError for Rational(0, 1) passed a negative Integer"
  fails "Rational#** when passed Integer returns the Rational value of self raised to the passed argument"
  fails "Rational#/ when passed an Integer raises a ZeroDivisionError when passed 0"
  fails "Rational#coerce returns the passed argument, self as Float, when given a Float"
  fails "Rational#divmod when passed an Integer returns the quotient as Integer and the remainder as Rational"
  fails "Struct#eql? returns false if any corresponding elements are not #eql?" # Rubyspec uses 1.eql?(1.0) which always returns true in compiled JS
  fails "Numeric#step with positional args when no block is given returned Enumerator size when self, stop or step is a Float and step is positive returns the difference between self and stop divided by the number of steps"
  fails "Numeric#step with keyword arguments when no block is given returned Enumerator size when self, stop or step is a Float and step is positive returns the difference between self and stop divided by the number of steps"
  fails "Numeric#step with mixed arguments when no block is given returned Enumerator size when self, stop or step is a Float and step is positive returns the difference between self and stop divided by the number of steps"
end
