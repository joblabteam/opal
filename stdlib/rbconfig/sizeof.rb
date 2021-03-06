# This file is not intended for real checks,
# but just to make happy libraries needing it.

RbConfig::SIZEOF = {
  "clock_t"              => 8,
  "double _Complex"      => 16,
  "double"               => 8,
  "float _Complex"       => 8,
  "float"                => 4,
  "int"                  => 4,
  "int128_t"             => 16,
  "int16_t"              => 2,
  "int32_t"              => 4,
  "int64_t"              => 8,
  "int8_t"               => 1,
  "intmax_t"             => 8,
  "intptr_t"             => 8,
  "int_fast16_t"         => 2,
  "int_fast32_t"         => 4,
  "int_fast64_t"         => 8,
  "int_fast8_t"          => 1,
  "int_least16_t"        => 2,
  "int_least32_t"        => 4,
  "int_least64_t"        => 8,
  "int_least8_t"         => 1,
  "long double _Complex" => 32,
  "long double"          => 16,
  "long long"            => 8,
  "long"                 => 8,
  "off_t"                => 8,
  "ptrdiff_t"            => 8,
  "short"                => 2,
  "sig_atomic_t"         => 4,
  "size_t"               => 8,
  "ssize_t"              => 8,
  "time_t"               => 8,
  "uint128_t"            => 16,
  "uint16_t"             => 2,
  "uint32_t"             => 4,
  "uint64_t"             => 8,
  "uint8_t"              => 1,
  "uintptr_t"            => 8,
  "void*"                => 8,
  "wchar_t"              => 4,
  "wctrans_t"            => 4,
  "wctype_t"             => 4,
  "wint_t"               => 4,
  "_Bool"                => 1,
  "__int128"             => 16,
}
