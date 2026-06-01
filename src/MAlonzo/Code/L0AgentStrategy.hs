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

module MAlonzo.Code.L0AgentStrategy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agent
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Flagship
import qualified MAlonzo.Code.FlagshipFull
import qualified MAlonzo.Code.PriceGrid
import qualified MAlonzo.Code.Proposal
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Seed
import qualified MAlonzo.Code.SimulationModel

-- L0AgentStrategy.l0Tick
d_l0Tick_6 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_l0Tick_6 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1)
      (coe MAlonzo.Code.PriceGrid.d_ratio_4 (coe v0) (coe v2))
-- L0AgentStrategy.tryL0Match
d_tryL0Match_14 ::
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agent.T_Agent_18 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  Maybe MAlonzo.Code.Flagship.T_RawMatch_6
d_tryL0Match_14 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (coe MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60)
              (coe
                 MAlonzo.Code.Data.Rational.Properties.du_drop'45''42''8804''42'_3534)
              (coe
                 MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880
                 (coe
                    MAlonzo.Code.Data.Integer.Base.d__'42'__316
                    (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v3))
                    (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                 (coe
                    MAlonzo.Code.Data.Integer.Base.d__'42'__316
                    (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1))
                    (coe
                       MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v3)))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Flagship.C_constructor_36 (coe v0) (coe v2)
                                 (coe
                                    MAlonzo.Code.Proposal.C_constructor_16
                                    (coe MAlonzo.Code.Agent.d_id_30 (coe v0)) (coe v1)
                                    (coe MAlonzo.Code.Agent.C_Buyer_4))
                                 (coe
                                    MAlonzo.Code.Proposal.C_constructor_16
                                    (coe MAlonzo.Code.Agent.d_id_30 (coe v2)) (coe v3)
                                    (coe MAlonzo.Code.Agent.C_Seller_6))
                                 (coe v7) (coe v3)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Data.Rational.Properties.d_'8804''45'refl_3606
                                       (coe v3))
                                    (coe v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- L0AgentStrategy.fromMaybe
d_fromMaybe_48 :: () -> Maybe AgdaAny -> [AgdaAny]
d_fromMaybe_48 ~v0 v1 = du_fromMaybe_48 v1
du_fromMaybe_48 :: Maybe AgdaAny -> [AgdaAny]
du_fromMaybe_48 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- L0AgentStrategy.runL0Matches
d_runL0Matches_54 ::
  Integer ->
  MAlonzo.Code.FlagshipFull.T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  [MAlonzo.Code.Flagship.T_RawMatch_6]
d_runL0Matches_54 v0 v1 v2
  = coe
      du_fromMaybe_48
      (coe
         d_tryL0Match_14 (coe MAlonzo.Code.FlagshipFull.d_buyer_16 (coe v1))
         (coe d_bidP_84 (coe v0) (coe v1) (coe v2))
         (coe MAlonzo.Code.FlagshipFull.d_seller_18 (coe v1))
         (coe d_askP_86 (coe v0) (coe v1) (coe v2)))
-- L0AgentStrategy._.i_b
d_i_b_80 ::
  Integer ->
  MAlonzo.Code.FlagshipFull.T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_i_b_80 ~v0 ~v1 v2 = du_i_b_80 v2
du_i_b_80 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_i_b_80 v0
  = coe
      MAlonzo.Code.Seed.du_drawAt_14 (coe v0)
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- L0AgentStrategy._.i_s
d_i_s_82 ::
  Integer ->
  MAlonzo.Code.FlagshipFull.T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_i_s_82 ~v0 ~v1 v2 = du_i_s_82 v2
du_i_s_82 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_i_s_82 v0
  = coe
      MAlonzo.Code.Seed.du_drawAt_14 (coe v0)
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- L0AgentStrategy._.bidP
d_bidP_84 ::
  Integer ->
  MAlonzo.Code.FlagshipFull.T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_bidP_84 v0 v1 v2
  = coe
      d_l0Tick_6 (coe v0)
      (coe MAlonzo.Code.FlagshipFull.d_maxP_20 (coe v1))
      (coe du_i_b_80 (coe v2))
-- L0AgentStrategy._.askP
d_askP_86 ::
  Integer ->
  MAlonzo.Code.FlagshipFull.T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_askP_86 v0 v1 v2
  = coe
      d_l0Tick_6 (coe v0)
      (coe MAlonzo.Code.FlagshipFull.d_maxP_20 (coe v1))
      (coe du_i_s_82 (coe v2))
-- L0AgentStrategy.concreteL0Sim
d_concreteL0Sim_90 ::
  Integer ->
  MAlonzo.Code.FlagshipFull.T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  [MAlonzo.Code.Flagship.T_RawMatch_6]
d_concreteL0Sim_90 v0 v1 = coe d_runL0Matches_54 (coe v0) (coe v1)
-- L0AgentStrategy.3ℚ
d_3ℚ_98 :: MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_3ℚ_98
  = coe
      MAlonzo.Code.Data.Rational.Base.du__'47'__156 (coe (3 :: Integer))
      (coe (1 :: Integer))
-- L0AgentStrategy.witnessEnv
d_witnessEnv_100 :: MAlonzo.Code.FlagshipFull.T_SimEnvironment_2
d_witnessEnv_100
  = coe
      MAlonzo.Code.FlagshipFull.C_constructor_28
      (coe MAlonzo.Code.Flagship.d_buyerWitness_42)
      (coe MAlonzo.Code.Flagship.d_sellerWitness_44) (coe d_3ℚ_98)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
         (coe
            MAlonzo.Code.Data.Rational.Properties.d__'8804''63'__3622
            (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
            (coe
               MAlonzo.Code.Data.Rational.Base.d__'8851'__332
               (coe MAlonzo.Code.Data.Rational.Base.d_1ℚ_180)
               (coe MAlonzo.Code.Flagship.d_3ℚ_4))))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
         (coe
            MAlonzo.Code.Data.Rational.Properties.d__'8804''63'__3622
            (coe MAlonzo.Code.Flagship.d_2ℚ_2) (coe d_3ℚ_98)))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- L0AgentStrategy.witnessSeed
d_witnessSeed_102 :: MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_witnessSeed_102
  = coe
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
      (coe
         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
         (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))
-- L0AgentStrategy.witnessSeedNegSurplus
d_witnessSeedNegSurplus_104 ::
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_witnessSeedNegSurplus_104
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
      (coe
         MAlonzo.Code.Data.Rational.Properties.d__'60''63'__3804
         (coe
            MAlonzo.Code.SimulationModel.d_l0RealizedSurplus_22
            (coe
               d_concreteL0Sim_90 (1 :: Integer) d_witnessEnv_100
               d_witnessSeed_102))
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
-- L0AgentStrategy.witnessForFlagship
d_witnessForFlagship_108 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_witnessForFlagship_108
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_witnessSeed_102)
      (coe d_witnessSeedNegSurplus_104)
