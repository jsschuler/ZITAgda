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

module MAlonzo.Code.FlagshipFull where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agent
import qualified MAlonzo.Code.AgentStrategy
import qualified MAlonzo.Code.BatchAuction
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Flagship
import qualified MAlonzo.Code.Institution
import qualified MAlonzo.Code.Seed
import qualified MAlonzo.Code.SimulationModel
import qualified MAlonzo.Code.Trace

-- FlagshipFull.SimEnvironment
d_SimEnvironment_2 = ()
data T_SimEnvironment_2
  = C_constructor_28 MAlonzo.Code.Agent.T_Agent_18
                     MAlonzo.Code.Agent.T_Agent_18 MAlonzo.Code.Data.Rational.Base.T_ℚ_6
                     MAlonzo.Code.Data.Rational.Base.T__'8804'__54
                     MAlonzo.Code.Data.Rational.Base.T__'8804'__54
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- FlagshipFull.SimEnvironment.buyer
d_buyer_16 :: T_SimEnvironment_2 -> MAlonzo.Code.Agent.T_Agent_18
d_buyer_16 v0
  = case coe v0 of
      C_constructor_28 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- FlagshipFull.SimEnvironment.seller
d_seller_18 :: T_SimEnvironment_2 -> MAlonzo.Code.Agent.T_Agent_18
d_seller_18 v0
  = case coe v0 of
      C_constructor_28 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- FlagshipFull.SimEnvironment.maxP
d_maxP_20 ::
  T_SimEnvironment_2 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_maxP_20 v0
  = case coe v0 of
      C_constructor_28 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- FlagshipFull.SimEnvironment.cap≥0
d_cap'8805'0_22 ::
  T_SimEnvironment_2 -> MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_cap'8805'0_22 v0
  = case coe v0 of
      C_constructor_28 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- FlagshipFull.SimEnvironment.v≤maxP
d_v'8804'maxP_24 ::
  T_SimEnvironment_2 -> MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_v'8804'maxP_24 v0
  = case coe v0 of
      C_constructor_28 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- FlagshipFull.SimEnvironment.hasInv
d_hasInv_26 ::
  T_SimEnvironment_2 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_hasInv_26 v0
  = case coe v0 of
      C_constructor_28 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- FlagshipFull.runMatches
d_runMatches_32 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  [MAlonzo.Code.Institution.T_Match_42]
d_runMatches_32 v0 v1 v2
  = coe
      MAlonzo.Code.BatchAuction.d_matchZip_78
      (coe d_bids_66 (coe v0) (coe v1) (coe v2))
      (coe d_asks_68 (coe v0) (coe v1) (coe v2))
-- FlagshipFull._._.buyer
d_buyer_46 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agent.T_Agent_18
d_buyer_46 ~v0 v1 ~v2 = du_buyer_46 v1
du_buyer_46 :: T_SimEnvironment_2 -> MAlonzo.Code.Agent.T_Agent_18
du_buyer_46 v0 = coe d_buyer_16 (coe v0)
-- FlagshipFull._._.cap≥0
d_cap'8805'0_48 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_cap'8805'0_48 ~v0 v1 ~v2 = du_cap'8805'0_48 v1
du_cap'8805'0_48 ::
  T_SimEnvironment_2 -> MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_cap'8805'0_48 v0 = coe d_cap'8805'0_22 (coe v0)
-- FlagshipFull._._.hasInv
d_hasInv_50 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_hasInv_50 ~v0 v1 ~v2 = du_hasInv_50 v1
du_hasInv_50 ::
  T_SimEnvironment_2 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_hasInv_50 v0 = coe d_hasInv_26 (coe v0)
-- FlagshipFull._._.maxP
d_maxP_52 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_maxP_52 ~v0 v1 ~v2 = du_maxP_52 v1
du_maxP_52 ::
  T_SimEnvironment_2 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_maxP_52 v0 = coe d_maxP_20 (coe v0)
-- FlagshipFull._._.seller
d_seller_54 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agent.T_Agent_18
d_seller_54 ~v0 v1 ~v2 = du_seller_54 v1
du_seller_54 :: T_SimEnvironment_2 -> MAlonzo.Code.Agent.T_Agent_18
du_seller_54 v0 = coe d_seller_18 (coe v0)
-- FlagshipFull._._.v≤maxP
d_v'8804'maxP_56 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_v'8804'maxP_56 ~v0 v1 ~v2 = du_v'8804'maxP_56 v1
du_v'8804'maxP_56 ::
  T_SimEnvironment_2 -> MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_v'8804'maxP_56 v0 = coe d_v'8804'maxP_24 (coe v0)
-- FlagshipFull._.i_b
d_i_b_58 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_i_b_58 ~v0 ~v1 v2 = du_i_b_58 v2
du_i_b_58 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_i_b_58 v0
  = coe
      MAlonzo.Code.Seed.du_drawAt_14 (coe v0)
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- FlagshipFull._.i_s
d_i_s_60 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_i_s_60 ~v0 ~v1 v2 = du_i_s_60 v2
du_i_s_60 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_i_s_60 v0
  = coe
      MAlonzo.Code.Seed.du_drawAt_14 (coe v0)
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- FlagshipFull._.bidEntry
d_bidEntry_62 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bidEntry_62 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_buyer_16 (coe v1))
      (coe
         MAlonzo.Code.AgentStrategy.du_makeBuyerBid_38 (coe v0)
         (coe d_buyer_16 (coe v1)) (coe du_i_b_58 (coe v2)))
-- FlagshipFull._.askEntry
d_askEntry_64 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_askEntry_64 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_seller_18 (coe v1))
      (coe
         MAlonzo.Code.AgentStrategy.du_makeSellerAsk_64 (coe v0)
         (coe d_seller_18 (coe v1)) (coe d_maxP_20 (coe v1))
         (coe du_i_s_60 (coe v2)) (coe d_hasInv_26 (coe v1)))
-- FlagshipFull._.bids
d_bids_66 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bids_66 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe d_bidEntry_62 (coe v0) (coe v1) (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- FlagshipFull._.asks
d_asks_68 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_asks_68 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe d_askEntry_64 (coe v0) (coe v1) (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- FlagshipFull.matchesToTrace
d_matchesToTrace_70 ::
  [MAlonzo.Code.Institution.T_Match_42] ->
  [MAlonzo.Code.Trace.T_Event_2]
d_matchesToTrace_70 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe MAlonzo.Code.Trace.C_TradeSettled_10) (coe v0)
-- FlagshipFull.concreteSim
d_concreteSim_76 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  [MAlonzo.Code.Trace.T_Event_2]
d_concreteSim_76 v0 v1 v2
  = coe
      d_matchesToTrace_70
      (coe d_runMatches_32 (coe v0) (coe v1) (coe v2))
-- FlagshipFull.concreteSimSurplusNonNeg
d_concreteSimSurplusNonNeg_88 ::
  Integer ->
  T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_concreteSimSurplusNonNeg_88 v0 v1 v2
  = coe
      MAlonzo.Code.Trace.d_realizedSurplusNonNeg_60
      (coe d_concreteSim_76 (coe v0) (coe v1) (coe v2))
-- FlagshipFull.concretePointwiseFlagship
d_concretePointwiseFlagship_104 ::
  Integer ->
  T_SimEnvironment_2 ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   [MAlonzo.Code.Flagship.T_RawMatch_6]) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_concretePointwiseFlagship_104 v0 v1 v2 v3
  = coe
      MAlonzo.Code.SimulationModel.du_flagshipPointwise_38
      (coe d_concreteSim_76 (coe v0) (coe v1)) (coe v2) (coe v3)
