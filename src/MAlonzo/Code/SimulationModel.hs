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

module MAlonzo.Code.SimulationModel where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Flagship
import qualified MAlonzo.Code.Probability
import qualified MAlonzo.Code.Trace

-- SimulationModel.SimFnL3
d_SimFnL3_6 :: Integer -> Integer -> ()
d_SimFnL3_6 = erased
-- SimulationModel.SimFnL0
d_SimFnL0_16 :: Integer -> Integer -> ()
d_SimFnL0_16 = erased
-- SimulationModel.l0RealizedSurplus
d_l0RealizedSurplus_22 ::
  [MAlonzo.Code.Flagship.T_RawMatch_6] ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_l0RealizedSurplus_22 v0
  = coe
      MAlonzo.Code.Probability.d_sumQ_38
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Flagship.d_rawSurplus_38) (coe v0))
-- SimulationModel.flagshipPointwise
d_flagshipPointwise_38 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   [MAlonzo.Code.Trace.T_Event_2]) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   [MAlonzo.Code.Flagship.T_RawMatch_6]) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_flagshipPointwise_38 ~v0 ~v1 v2 v3 v4
  = du_flagshipPointwise_38 v2 v3 v4
du_flagshipPointwise_38 ::
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   [MAlonzo.Code.Trace.T_Event_2]) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   [MAlonzo.Code.Flagship.T_RawMatch_6]) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_flagshipPointwise_38 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Data.Rational.Properties.d_'60''45''8804''45'trans_3732
                (coe d_l0RealizedSurplus_22 (coe v1 v3))
                (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
                (coe MAlonzo.Code.Trace.d_realizedSurplus_30 (coe v0 v3)) (coe v4)
                (coe MAlonzo.Code.Trace.d_realizedSurplusNonNeg_60 (coe v0 v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- SimulationModel.flagshipExpected
d_flagshipExpected_62 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   [MAlonzo.Code.Trace.T_Event_2]) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   [MAlonzo.Code.Flagship.T_RawMatch_6]) ->
  [MAlonzo.Code.Data.Vec.Base.T_Vec_28] ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   MAlonzo.Code.Data.Rational.Base.T__'8804'__54) ->
  MAlonzo.Code.Probability.T_StrictAt_16 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_flagshipExpected_62 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 v8
  = du_flagshipExpected_62 v2 v3 v4 v5 v8
du_flagshipExpected_62 ::
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   [MAlonzo.Code.Trace.T_Event_2]) ->
  (MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
   [MAlonzo.Code.Flagship.T_RawMatch_6]) ->
  [MAlonzo.Code.Data.Vec.Base.T_Vec_28] ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Probability.T_StrictAt_16 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_flagshipExpected_62 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Probability.d_sumQStrict_88
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe (\ v5 -> d_l0RealizedSurplus_22 (coe v1 v5)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v2)))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe (\ v5 -> MAlonzo.Code.Trace.d_realizedSurplus_30 (coe v0 v5)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v2)))
      (coe v4)
