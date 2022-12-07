module Utils.Time

import Utils.Num
import Data.Fin
import Data.String.Parser
import Data.Vect
import Data.String
import Data.Fin.Extra
import Utils.Misc
import Decidable.Equality
import Derive.Prelude
import Generics.Derive

%hide Generics.Derive.Eq
%hide Generics.Derive.Ord
%hide Generics.Derive.Show

%language ElabReflection

public export
data Month : Type where
  January : Month
  February : Month
  March : Month
  April : Month
  May : Month
  June : Month
  July : Month
  August : Month
  September : Month
  October : Month
  November : Month
  December : Month

export
next_month : Month -> Month
next_month January    = February
next_month February   = March
next_month March      = April
next_month April      = May
next_month May        = June
next_month June       = July
next_month July       = August
next_month August     = September
next_month September  = October
next_month October    = November
next_month November   = December
next_month December   = January

export
prev_month : Month -> Month
prev_month January    = December
prev_month February   = January
prev_month March      = February
prev_month April      = March
prev_month May        = April
prev_month June       = May
prev_month July       = June
prev_month August     = July
prev_month September  = August
prev_month October    = September
prev_month November   = October
prev_month December   = November

public export
next_prev_month : (m : Month) -> (next_month $ prev_month m) = m
next_prev_month January    = Refl
next_prev_month February   = Refl
next_prev_month March      = Refl
next_prev_month April      = Refl
next_prev_month May        = Refl
next_prev_month June       = Refl
next_prev_month July       = Refl
next_prev_month August     = Refl
next_prev_month September  = Refl
next_prev_month October    = Refl
next_prev_month November   = Refl
next_prev_month December   = Refl

public export
prev_next_month : (m : Month) -> (prev_month $ next_month m) = m
prev_next_month January    = Refl
prev_next_month February   = Refl
prev_next_month March      = Refl
prev_next_month April      = Refl
prev_next_month May        = Refl
prev_next_month June       = Refl
prev_next_month July       = Refl
prev_next_month August     = Refl
prev_next_month September  = Refl
prev_next_month October    = Refl
prev_next_month November   = Refl
prev_next_month December   = Refl

export
nat_to_month : Nat -> Maybe Month
nat_to_month 1  = Just January
nat_to_month 2  = Just February
nat_to_month 3  = Just March
nat_to_month 4  = Just April
nat_to_month 5  = Just May
nat_to_month 6  = Just June
nat_to_month 7  = Just July
nat_to_month 8  = Just August
nat_to_month 9  = Just September
nat_to_month 10 = Just October
nat_to_month 11 = Just November
nat_to_month 12 = Just December
nat_to_month _ = Nothing

export
fin_to_month : Fin 12 -> Month
fin_to_month 0  = January
fin_to_month 1  = February
fin_to_month 2  = March
fin_to_month 3  = April
fin_to_month 4  = May
fin_to_month 5  = June
fin_to_month 6  = July
fin_to_month 7  = August
fin_to_month 8  = September
fin_to_month 9  = October
fin_to_month 10 = November
fin_to_month 11 = December

export
month_to_nat : Month -> Nat
month_to_nat January   = 1
month_to_nat February  = 2
month_to_nat March     = 3
month_to_nat April     = 4
month_to_nat May       = 5
month_to_nat June      = 6
month_to_nat July      = 7
month_to_nat August    = 8
month_to_nat September = 9
month_to_nat October   = 10
month_to_nat November  = 11
month_to_nat December  = 12

export
month_num_of_dates : Integer -> Month -> Nat
month_num_of_dates _ January = 31
month_num_of_dates year February =
  if year `mod` 4 /= 0 then 28
    else if year `mod` 100 /= 0 then 29
    else if year `mod` 400 /= 0 then 28
    else 29
month_num_of_dates _ March = 31
month_num_of_dates _ April = 30
month_num_of_dates _ May = 31
month_num_of_dates _ June = 30
month_num_of_dates _ July = 31
month_num_of_dates _ August = 31
month_num_of_dates _ September = 30
month_num_of_dates _ October = 31
month_num_of_dates _ November = 30
month_num_of_dates _ December = 31

%runElab derive "Month" [Generic, Meta, DecEq, Eq, Ord, Show]

public export
data FinNonZero : Fin n -> Type where
  FSIsNonZero : FinNonZero (FS x)

show_nat_pad : Nat -> Nat -> String
show_nat_pad p n =
  let str = show n
      pad_len = minus p $ length str
      pad = replicate pad_len '0'
  in pad <+> str

show_fin_pad : Nat -> Fin n -> String
show_fin_pad p n = show_nat_pad p $ finToNat n

public export
record Date where
  constructor MkDate
  year : Integer
  month : Month
  day : Fin (S (month_num_of_dates year month))
  day_non_zero : FinNonZero day

export
epoch_date : Date
epoch_date = MkDate 1970 January 1 FSIsNonZero

export
Eq Date where
  a == b =
    case decEq a.year b.year of
      Yes prf0 =>
        case decEq a.month b.month of
          Yes prf1 => a.day == (rewrite prf0 in rewrite prf1 in b.day)
          No _ => False
      No _ => False

export
Ord Date where
  a `compare` b =
    case decEq a.year b.year of
      Yes prf0 =>
        case decEq a.month b.month of
          Yes prf1 =>
            let b_day = rewrite prf0 in rewrite prf1 in b.day
            in a.day `compare` b_day
          No _ => a.month `compare` b.month
      No _ => a.year `compare` b.year

export
Show Date where
  show date =
    (show $ date.year)
    <+> "/"
    <+> (show $ month_to_nat date.month)
    <+> "/"
    <+> (show_fin_pad 2 date.day)

date_to_tuple : Date -> (Integer, Integer, Integer)
date_to_tuple date = (date.year, natToInteger $ pred $ month_to_nat date.month, finToInteger date.day - 1)

date_to_normalized_tuple : Date -> (Integer, Month, Integer)
date_to_normalized_tuple date = (date.year, date.month, finToInteger date.day - 1)

tuple_normalize_month : (Integer, Integer, Integer) -> (Integer, Month, Integer)
tuple_normalize_month (year, month, day) =
  ( if month >= 0 then year + month `div` 12 else year + ((month + 1) `div` 12) - 1
  , fin_to_month $ modFinNZ (integerToNat $ month `mod'` 12) 12 SIsNonZero
  , day)

tuple_normalize_next_month : (Integer, Month, Integer) -> (Integer, Month, Integer)
tuple_normalize_next_month (year, month, day) =
  let next = next_month month
      new_year = case month of { December => year + 1; _ => year; }
  in (new_year, next, day - (natToInteger $ month_num_of_dates year month))

tuple_normalize_prev_month : (Integer, Month, Integer) -> (Integer, Month, Integer)
tuple_normalize_prev_month (year, month, day) =
  let prev = prev_month month
      new_year = case month of { January => year - 1; _ => year; }
  in (new_year, prev, day + (natToInteger $ month_num_of_dates year prev))

tuple_normalize_day : (Integer, Month, Integer) -> Date
tuple_normalize_day (year, month, day) =
  case integerToFin day (month_num_of_dates year month) of
    Just day' => MkDate year month (FS day') FSIsNonZero
    Nothing =>
      if day < 0
        then tuple_normalize_day $ tuple_normalize_prev_month (year, month, day)
        else tuple_normalize_day $ tuple_normalize_next_month (year, month, day)

tuple_normalize_date : (Integer, Integer, Integer) -> Date
tuple_normalize_date = tuple_normalize_day . tuple_normalize_month

days_between_dates' : (Integer, Month, Integer) -> (Integer, Month, Integer) -> Integer
days_between_dates' a@(a_year, a_month, a_day) b@(b_year, b_month, b_day) =
  case collapse_ordering [a_year `compare` b_year, a_month `compare` b_month] of
    LT => days_between_dates' (tuple_normalize_next_month a) b
    GT => days_between_dates' (tuple_normalize_prev_month a) b
    EQ => a_day - b_day

export
days_between_dates : Date -> Date -> Integer
days_between_dates a b = days_between_dates' (date_to_normalized_tuple a) (date_to_normalized_tuple b)

day_in_seconds : Nat
day_in_seconds = 24 * 60 * 60

day_in_milliseconds : Nat
day_in_milliseconds = 24 * 60 * 60 * 1000

day_in_seconds' : Integer
day_in_seconds' = natToInteger day_in_seconds

day_in_milliseconds' : Integer
day_in_milliseconds' = natToInteger day_in_milliseconds

public export
record DateTime where
  constructor MkDateTime
  date : Date
  hour : Fin 24
  minute : Fin 60
  second : Fin 60
  subsecond : Fin 1000
  offset_plus_or_minus : Bool
  hour_offset : Nat
  minute_offset : Fin 60

second_of_day : Nat -> (Fin 24, Fin 60, Fin 60)
second_of_day x =
  let second = modFinNZ x 60 SIsNonZero
      x = divNatNZ x 60 SIsNonZero
      minute = modFinNZ x 60 SIsNonZero
      x = divNatNZ x 60 SIsNonZero
      hour = modFinNZ x 24 SIsNonZero
  in (hour, minute, second)

export
epoch_to_datetime : Integer -> DateTime
epoch_to_datetime epoch =
  let (hour, minute, second) = second_of_day $ integerToNat $ epoch `mod'` day_in_seconds'
      dayno = if epoch >= 0 then epoch `div` day_in_seconds' else ((epoch + 1) `div` day_in_seconds') - 1
      date = tuple_normalize_date (1970, 0, dayno)
  in MkDateTime date hour minute second 0 True 0 0

export
millisecond_epoch_to_datetime : Integer -> DateTime
millisecond_epoch_to_datetime epoch =
  let subsecond' = integerToNat $ epoch `mod'` 1000
  in { subsecond := modFinNZ subsecond' 1000 SIsNonZero } (epoch_to_datetime $ epoch `div` 1000)

datetime_to_epoch' : DateTime -> Integer
datetime_to_epoch' datetime =
  (days_between_dates datetime.date epoch_date) * day_in_seconds'
  + (finToInteger datetime.hour * 60 * 60)
  + (finToInteger datetime.minute * 60)
  + (finToInteger datetime.second)

millisecond_datetime_to_epoch' : DateTime -> Integer
millisecond_datetime_to_epoch' datetime = (datetime_to_epoch' datetime) * 1000 + finToInteger datetime.subsecond

export
gmt_datetime : DateTime -> DateTime
gmt_datetime datetime =
  let epoch = millisecond_datetime_to_epoch' datetime
      offset = (1000 * 3600 * natToInteger datetime.hour_offset) + (1000 * 60 * finToInteger datetime.minute_offset)
      epoch = if datetime.offset_plus_or_minus then epoch - offset else epoch + offset
  in millisecond_epoch_to_datetime epoch

export
datetime_to_epoch : DateTime -> Integer
datetime_to_epoch = datetime_to_epoch' . gmt_datetime

export
millisecond_datetime_to_epoch : DateTime -> Integer
millisecond_datetime_to_epoch = millisecond_datetime_to_epoch' . gmt_datetime

export
Show DateTime where
  show datetime =
    (show $ datetime.date)
    <+> " "
    <+> (show_fin_pad 2 datetime.hour)
    <+> ":"
    <+> (show_fin_pad 2 datetime.minute)
    <+> ":"
    <+> (show_fin_pad 2 datetime.second)
    <+> "."
    <+> (show_fin_pad 3 datetime.subsecond)
    <+> " "
    <+> (if datetime.offset_plus_or_minus then "+" else "-")
    <+> (show_nat_pad 2 datetime.hour_offset)
    <+> ":"
    <+> (show_fin_pad 2 datetime.minute_offset)

fromDigits : Num a => (Fin 10 -> a) -> List (Fin 10) -> a
fromDigits f xs = foldl addDigit 0 xs
  where
    addDigit : a -> Fin 10 -> a
    addDigit num d = 10*num + f d

natFromDigits : List (Fin 10) -> Nat
natFromDigits = fromDigits finToNat

natFromNDigits : Monad m => Nat -> ParseT m Nat
natFromNDigits n = natFromDigits . toList <$> ntimes n digit

finNFromNDigits : Monad m => String -> (n : Nat) -> Nat -> ParseT m (Fin n)
finNFromNDigits name bound n = do
  number <- natFromNDigits n
  case natToFin number bound of
    Just fin => pure fin
    Nothing => fail $ "invalid " <+> name <+> ": " <+> show number

export
utc_time : Monad m => ParseT m DateTime
utc_time = do
  yy <- natFromDigits . toList <$> ntimes 2 digit
  mm <- natFromDigits . toList <$> ntimes 2 digit
  let year = if yy < 50 then 2000 + natToInteger yy else 1900 + natToInteger yy
  let Just month = nat_to_month mm
  | Nothing => fail $ "invalid month: " <+> show mm
  FS fs_day <- finNFromNDigits "day" (S $ month_num_of_dates year month) 2
  | FZ => fail "invalid day: 0"
  hour <- finNFromNDigits "hour" 24 2
  minute <- finNFromNDigits "minute" 60 2
  second <- option 0 $ finNFromNDigits "second" 60 2
  sign <- satisfy (const True)
  let date = MkDate year month (FS fs_day) FSIsNonZero
  let mk_date_time = MkDateTime date hour minute second 0
  case sign of
    'Z' => pure $ mk_date_time True 0 0
    '+' => uncurry (mk_date_time True) <$> utc_time_offset
    '-' => uncurry (mk_date_time False) <$> utc_time_offset
    err => fail $ "unrecognized timezone sign: " <+> show err
  where
    utc_time_offset : ParseT m (Nat, Fin 60)
    utc_time_offset = do
      hh <- natFromDigits . toList <$> ntimes 2 digit
      minute_off <- finNFromNDigits "minute offset" 60 2
      pure (hh, minute_off)

export
generalized_time : Monad m => ParseT m DateTime
generalized_time = do
  year <- natToInteger . natFromDigits . toList <$> ntimes 4 digit
  mm <- natFromDigits . toList <$> ntimes 2 digit
  let Just month = nat_to_month mm
  | Nothing => fail $ "invalid month: " <+> show mm

  FS fs_day <- finNFromNDigits "day" (S $ month_num_of_dates year month) 2
  | FZ => fail "invalid day: 0"

  hour <- finNFromNDigits "hour" 24 2
  minute <- option 0 $ finNFromNDigits "minute" 60 2
  second <- option 0 $ finNFromNDigits "second" 60 2

  subsecond <- option 0 subsecond

  sign <- satisfy (const True)
  let date = MkDate year month (FS fs_day) FSIsNonZero
  let mk_date_time = MkDateTime date hour minute second subsecond
  case sign of
    'Z' => pure $ mk_date_time True 0 0
    '+' => uncurry (mk_date_time True) <$> utc_time_offset
    '-' => uncurry (mk_date_time False) <$> utc_time_offset
    err => fail $ "unrecognized timezone sign: " <+> show err
  where
    utc_time_offset : ParseT m (Nat, Fin 60)
    utc_time_offset = do
      hh <- natFromDigits . toList <$> ntimes 2 digit
      minute_off <- finNFromNDigits "minute offset" 60 2
      pure (hh, minute_off)
    subsecond : ParseT m (Fin 1000)
    subsecond = do
      a <- char '.' *> natFromNDigits 1
      b <- option 0 $ natFromNDigits 1
      c <- option 0 $ natFromNDigits 1
      case natToFin (a * 100 + b * 10 + c) 1000 of
        Just x => pure x
        Nothing => fail "how"

export
parse_utc_time : String -> Either String DateTime
parse_utc_time = map fst . parse utc_time

export
parse_generalized_time : String -> Either String DateTime
parse_generalized_time = map fst . parse generalized_time
