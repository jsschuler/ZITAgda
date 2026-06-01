{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Trace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.GCD
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Institution
import qualified MAlonzo.Code.Proposal
import qualified MAlonzo.Code.Surplus

-- Trace.Event
d_Event_2 = ()
data T_Event_2
  = C_OrderSubmitted_4 Integer MAlonzo.Code.Proposal.T_Proposal_2 |
    C_OrderRejected_6 Integer MAlonzo.Code.Proposal.T_Proposal_2 |
    C_OrderAccepted_8 Integer MAlonzo.Code.Proposal.T_Proposal_2 |
    C_TradeSettled_10 MAlonzo.Code.Institution.T_Match_42 |
    C_AuctionCleared_12 MAlonzo.Code.Data.Rational.Base.T_ℚ_6
-- Trace.Trace
d_Trace_14 :: ()
d_Trace_14 = erased
-- Trace.tradesView
d_tradesView_16 ::
  [T_Event_2] -> [MAlonzo.Code.Institution.T_Match_42]
d_tradesView_16 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_tradesView_16 (coe v2) in
           coe
             (case coe v1 of
                C_TradeSettled_10 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                       (coe d_tradesView_16 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Trace.sumSurplus
d_sumSurplus_24 ::
  [MAlonzo.Code.Institution.T_Match_42] ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_sumSurplus_24 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Rational.Base.d__'43'__270
             (coe MAlonzo.Code.Surplus.d_surplus_16 (coe v1))
             (coe d_sumSurplus_24 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Trace.realizedSurplus
d_realizedSurplus_30 ::
  [T_Event_2] -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_realizedSurplus_30 v0
  = coe d_sumSurplus_24 (coe d_tradesView_16 (coe v0))
-- Trace.0≤a+b
d_0'8804'a'43'b_38 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_0'8804'a'43'b_38 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Rational.Properties.d_'43''45'mono'45''8804'_4360
      (coe
         MAlonzo.Code.Data.Rational.Base.C_mkℚ_24
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe (0 :: Integer))
               (coe (1 :: Integer))))
         (0 :: Integer))
      (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Base.C_mkℚ_24
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe (0 :: Integer))
               (coe (1 :: Integer))))
         (0 :: Integer))
      (coe v1) (coe v2) (coe v3)
-- Trace.sumSurplusNonNeg
d_sumSurplusNonNeg_52 ::
  [MAlonzo.Code.Institution.T_Match_42] ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_sumSurplusNonNeg_52 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.Rational.Properties.d_'8804''45'refl_3606
             (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
      (:) v1 v2
        -> coe
             d_0'8804'a'43'b_38 (coe MAlonzo.Code.Surplus.d_surplus_16 (coe v1))
             (coe d_sumSurplus_24 (coe v2))
             (coe MAlonzo.Code.Surplus.d_surplusNonNeg_22 (coe v1))
             (coe d_sumSurplusNonNeg_52 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Trace.realizedSurplusNonNeg
d_realizedSurplusNonNeg_60 ::
  [T_Event_2] -> MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_realizedSurplusNonNeg_60 v0
  = coe d_sumSurplusNonNeg_52 (coe d_tradesView_16 (coe v0))
