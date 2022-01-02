module Network.TLS.Verify

import Network.TLS
import Network.TLS.Certificate
import Network.TLS.Handshake
import Utils.Misc
import Utils.Bytes
import Data.String
import Data.List
import Data.List.Lazy
import Data.List1
import Data.Vect
import Utils.IPAddr
import Data.Either
import System
import Control.Monad.Error.Either
import Control.Monad.Trans

%hide Network.TLS.Handshake.Message.Certificate

domain_predicate : String -> Maybe (String -> Bool)
domain_predicate predicate = do
  let parts = split ('.' ==) predicate
  guard $ verify_predicate parts
  Just (apply_predicate parts . split ('.' == ))
  where
    str_eq : String -> String -> Lazy Bool
    str_eq "*" _ = delay True
    str_eq _ "*" = delay True
    str_eq a b = delay (a == b)
    apply_predicate : List1 String -> List1 String -> Bool
    apply_predicate a b = (length a == length b) && (and $ zipWith str_eq a b)
    verify_predicate : List1 String -> Bool
    verify_predicate ("*" ::: []) = False
    verify_predicate ("*" ::: [_]) = False
    verify_predicate ("*" ::: [_, ""]) = False
    verify_predicate ("*" ::: xs) = and $ map (delay . not . isInfixOf "*") xs
    verify_predicate xs = and $ map (delay . not . isInfixOf "*") (toList xs)

domain_predicate' : String -> (String -> Bool)
domain_predicate' predicate =
  case domain_predicate predicate of
    Nothing => const False
    Just f => f

check_ipv4_address : List GeneralName -> IPv4Addr -> Bool
check_ipv4_address (IPv4Addr addr' :: xs) addr = if addr == addr' then True else check_ipv4_address xs addr
check_ipv4_address (x :: xs) addr = check_ipv4_address xs addr
check_ipv4_address [] _ = False

check_ipv6_address : List GeneralName -> IPv6Addr -> Bool
check_ipv6_address (IPv6Addr addr' :: xs) addr = if addr == addr' then True else check_ipv6_address xs addr
check_ipv6_address (x :: xs) addr = check_ipv6_address xs addr
check_ipv6_address [] _ = False

check_dns_name : List GeneralName -> String -> Bool
check_dns_name (DNSName predicate :: xs) name = if (domain_predicate' predicate) name then True else check_dns_name xs name
check_dns_name (x :: xs) name = check_dns_name xs name
check_dns_name [] _ = False

Identifier : Type
Identifier = Eithers [IPv4Addr, IPv6Addr, String]

check_cert_timestamp : HasIO io => Certificate -> io Bool
check_cert_timestamp cert = (\t => t > cert.valid_not_before && t < cert.valid_not_after) <$> time

find_certificate : Identifier -> List Certificate -> Maybe Certificate
find_certificate identifier certs = choice $ map (delay . is_certificate identifier) certs
  where
    is_certificate : Identifier -> Certificate -> Maybe Certificate
    is_certificate (Left x)          cert = guard (check_ipv4_address (certificate_subject_names cert) x) $> cert
    is_certificate (Right (Left x))  cert = guard (check_ipv6_address (certificate_subject_names cert) x) $> cert
    is_certificate (Right (Right x)) cert = guard (check_dns_name (certificate_subject_names cert) x) $> cert

to_identifier : String -> Identifier
to_identifier hostname =
  case parse_ipv4 hostname of
    Right x => Left x
    Left _ =>
      case parse_ipv6 hostname of
        Right x => Right (Left x)
        Left _ => Right (Right hostname)

check_leaf_certificate : HasIO io => Certificate -> EitherT String io ()
check_leaf_certificate cert = do
  True <- check_cert_timestamp cert
  | False => throwE $ "expired certificate: " <+> show cert
  let Just key_usage = extract_extension KeyUsage cert
  | Nothing => throwE $ "certificate does not specify key usage: " <+> show cert
  let True = key_usage.digital_signature
  | False => throwE $ "certificate key usage does not allow digital signature: " <+> show cert
  pure ()

check_branch_certificate : HasIO io => Nat -> Certificate -> EitherT String io ()
check_branch_certificate depth cert = do
  True <- check_cert_timestamp cert
  | False => throwE $ "expired certificate: " <+> show cert
  let Just key_usage = extract_extension KeyUsage cert
  | Nothing => throwE $ "certificate does not specify key usage: " <+> show cert
  let Just basic_constraint = extract_extension BasicConstraint cert
  | Nothing => throwE $ "certificate does not specify basic constraint: " <+> show cert
  let True = basic_constraint.ca
  | False => throwE $ "certificate is not a CA: " <+> show cert
  let True = basic_constraint.path_len `cmp` depth
  | False => throwE $ "certificate CA depth reached: " <+> show cert
  let True = key_usage.key_cert_sign
  | False => throwE $ "certificate key usage does not allow signing certificates: " <+> show cert
  pure ()
  where
    cmp : Maybe Nat -> Nat -> Bool
    cmp Nothing _ = True
    cmp (Just a) b = b <= a

-- TODO: implement this
verify_certificate_signature : Certificate -> Certificate -> Bool
verify_certificate_signature subject issuer = True

has_intersect : Eq a => List a -> List a -> Bool
has_intersect [] y = False
has_intersect x [] = False
has_intersect (x :: xs) y = if any (x ==) y then True else has_intersect xs y

auth_key_id_predicate : ExtAuthorityKeyIdentifier -> (Certificate -> Bool)
auth_key_id_predicate (MkExtAuthorityKeyIdentifier Nothing [] Nothing) = const False
auth_key_id_predicate auth_key_id = go auth_key_id
  where
    def : Maybe Bool -> Bool
    def Nothing = True
    def (Just a) = a
    go0 : ExtAuthorityKeyIdentifier -> Certificate -> Bool
    go0 auth_key_id cert = def (map (\i => i == cert.cert_public_key_id) auth_key_id.key_identifier)
    go1 : ExtAuthorityKeyIdentifier -> Certificate -> Bool
    go1 auth_key_id cert = def (map (\i => i == cert.serial_number) auth_key_id.serial_number)
    go2 : ExtAuthorityKeyIdentifier -> Certificate -> Bool
    go2 auth_key_id cert =
      case auth_key_id.general_names of
        [] => True
        gn => has_intersect gn $ certificate_subject_names cert
    go : ExtAuthorityKeyIdentifier -> Certificate -> Bool
    go a b = go0 a b && go1 a b && go2 a b

flatten : Maybe (LazyList a) -> LazyList a
flatten Nothing = []
flatten (Just a) = a

verify_certificate_chain : HasIO io => Nat -> List Certificate -> List Certificate -> Certificate -> EitherT String io ()
verify_certificate_chain depth trusted untrusted current = do
  let alternate = map (True,) $ flatten $ do
    ext <- extract_extension AuthorityKeyIdentifier current
    let predicate = auth_key_id_predicate ext
    pure $ filter predicate $ Lazy.fromList trusted

  let in_chain = filter (\(_,c) => c.subject == current.issuer) (map (False,) untrusted <+> map (True,) trusted)
  let all_candidates = fromList in_chain <+> alternate

  case all_candidates of
    [] => throwE $ "cannot find issuer for: " <+> show current
    all => Lazy.choice $ map (\(should_trust,next) => go should_trust next current) all
  where
    go : Bool -> Certificate -> Certificate -> EitherT String io ()
    go should_trust next current =
      case should_trust of
        False => do
          check_branch_certificate depth next
          let True = verify_certificate_signature current next
          | False => throwE $ "certificate failed for subject: " <+> show current <+> ", issuer: " <+> show next
          verify_certificate_chain (S depth) trusted untrusted next
        True => do
          -- replace the self signed certificate with the one we trust
          let Just next = find (\c => c.subject == next.subject) trusted
          | Nothing => throwE $ "root certificate not trusted: " <+> show next
          check_branch_certificate depth next
          let True = verify_certificate_signature current next
          | False => throwE $ "certificate failed for subject: " <+> show current <+> ", issuer: " <+> show next
          pure ()

liftE : Monad m => Either a b -> EitherT a m b
liftE x = MkEitherT $ pure x

export
certificate_check : List Certificate -> String -> CertificateCheck IO
certificate_check trusted hostname cert = runEitherT $ do
  let certificates = body <$> cert.certificates
  ok <- liftE $ the _ $ traverse parse_certificate certificates
  let identifer = to_identifier hostname
  let Just cert = find_certificate identifer ok
  | Nothing => throwE "cannot find certificate"
  check_leaf_certificate cert
  verify_certificate_chain Z trusted ok cert
