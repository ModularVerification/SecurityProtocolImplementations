module RecvSentMsgDefinitions

open SecrecyLabels
module A = LabeledCryptoAPI
module R = LabeledRuntimeAPI

let ppred i s pk m = True
let apred i s k m ad = True
let spred i s k m = True
let mpred i s k m = True

let usage_preds : A.usage_preds = {
  A.can_pke_encrypt = ppred;
  A.can_aead_encrypt =  apred;
  A.can_sign = spred;
  A.can_mac = mpred
}

let global_usage : A.global_usage = {
  A.key_usages = A.default_key_usages;
  A.usage_preds = usage_preds;
}

let epred i s ev = True
let sess_inv i p si vi st =
  A.is_msg global_usage i st (readers [V p si vi])

let example: R.preds = {
  R.global_usage = global_usage;
  R.trace_preds = {
    R.can_trigger_event = epred;
    R.session_st_inv = sess_inv;
    R.session_st_inv_later = (fun i j p si vi st -> ());
    R.session_st_inv_lemma = (fun i p si vi st -> ())
  }
}

let msg i l = A.msg global_usage i l
