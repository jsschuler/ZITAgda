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

module MAlonzo.Code.Main where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.IO
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agent
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Data.Rational.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Unit.Polymorphic.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.FlagshipFull
import qualified MAlonzo.Code.IO.Base
import qualified MAlonzo.Code.IO.Finite
import qualified MAlonzo.Code.L0AgentStrategy
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Seed
import qualified MAlonzo.Code.SimulationModel
import qualified MAlonzo.Code.Trace

-- Main.3ℚ
d_3ℚ_4 :: MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_3ℚ_4
  = coe
      MAlonzo.Code.Data.Rational.Base.du__'47'__156 (coe (3 :: Integer))
      (coe (1 :: Integer))
-- Main.4ℚ
d_4ℚ_6 :: MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_4ℚ_6
  = coe
      MAlonzo.Code.Data.Rational.Base.du__'47'__156 (coe (4 :: Integer))
      (coe (1 :: Integer))
-- Main.marketBuyer
d_marketBuyer_8 :: MAlonzo.Code.Agent.T_Agent_18
d_marketBuyer_8
  = coe
      MAlonzo.Code.Agent.C_constructor_40 (coe (2 :: Integer))
      (coe MAlonzo.Code.Agent.C_Buyer_4)
      (coe MAlonzo.Code.Agent.C_constructor_14 (coe d_3ℚ_4)) (coe d_4ℚ_6)
      (coe (0 :: Integer))
-- Main.marketSeller
d_marketSeller_10 :: MAlonzo.Code.Agent.T_Agent_18
d_marketSeller_10
  = coe
      MAlonzo.Code.Agent.C_constructor_40 (coe (3 :: Integer))
      (coe MAlonzo.Code.Agent.C_Seller_6)
      (coe
         MAlonzo.Code.Agent.C_constructor_14
         (coe MAlonzo.Code.Data.Rational.Base.d_1ℚ_180))
      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe (1 :: Integer))
-- Main.marketEnv
d_marketEnv_12 :: MAlonzo.Code.FlagshipFull.T_SimEnvironment_2
d_marketEnv_12
  = coe
      MAlonzo.Code.FlagshipFull.C_constructor_28 (coe d_marketBuyer_8)
      (coe d_marketSeller_10) (coe d_4ℚ_6)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
         (coe
            MAlonzo.Code.Data.Rational.Properties.d__'8804''63'__3622
            (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
            (coe
               MAlonzo.Code.Data.Rational.Base.d__'8851'__332 (coe d_3ℚ_4)
               (coe d_4ℚ_6))))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
         (coe
            MAlonzo.Code.Data.Rational.Properties.d__'8804''63'__3622
            (coe MAlonzo.Code.Data.Rational.Base.d_1ℚ_180) (coe d_4ℚ_6)))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Main.f0
d_f0_14 :: MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_f0_14 = coe MAlonzo.Code.Data.Fin.Base.C_zero_12
-- Main.f1
d_f1_16 :: MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_f1_16
  = coe
      MAlonzo.Code.Data.Fin.Base.C_suc_16
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- Main.f2
d_f2_18 :: MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_f2_18
  = coe
      MAlonzo.Code.Data.Fin.Base.C_suc_16
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Main.f3
d_f3_20 :: MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_f3_20
  = coe
      MAlonzo.Code.Data.Fin.Base.C_suc_16
      (coe
         MAlonzo.Code.Data.Fin.Base.C_suc_16
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Main.allSeeds4
d_allSeeds4_22 :: [MAlonzo.Code.Data.Vec.Base.T_Vec_28]
d_allSeeds4_22
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f0_14
         (coe
            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f0_14
            (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f0_14
            (coe
               MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f1_16
               (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f0_14
               (coe
                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f2_18
                  (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f0_14
                  (coe
                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f3_20
                     (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f1_16
                     (coe
                        MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f0_14
                        (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f1_16
                        (coe
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f1_16
                           (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f1_16
                           (coe
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f2_18
                              (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f1_16
                              (coe
                                 MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f3_20
                                 (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f2_18
                                 (coe
                                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f0_14
                                    (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f2_18
                                    (coe
                                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f1_16
                                       (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f2_18
                                       (coe
                                          MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f2_18
                                          (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f2_18
                                          (coe
                                             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f3_20
                                             (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f3_20
                                             (coe
                                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f0_14
                                                (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f3_20
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f1_16
                                                   (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 d_f3_20
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                      d_f2_18
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                      d_f3_20
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         d_f3_20
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))
-- Main.simRow
d_simRow_24 ::
  MAlonzo.Code.FlagshipFull.T_SimEnvironment_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> MAlonzo.Code.IO.Base.T_IO_20
d_simRow_24 v0 v1
  = coe
      MAlonzo.Code.IO.Finite.d_putStrLn_28
      (coe MAlonzo.Code.Level.d_0ℓ_22)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("  [" :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (coe
               MAlonzo.Code.Data.Nat.Show.d_show_56
               (coe
                  MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                  (coe
                     MAlonzo.Code.Seed.du_drawAt_14 (coe v1)
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               ("," :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (coe
                     MAlonzo.Code.Data.Nat.Show.d_show_56
                     (coe
                        MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                        (coe
                           MAlonzo.Code.Seed.du_drawAt_14 (coe v1)
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("]" :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("  bid=" :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (MAlonzo.Code.Data.Rational.Show.d_show_6
                              (coe
                                 MAlonzo.Code.L0AgentStrategy.d_l0Tick_6 (coe (3 :: Integer))
                                 (coe MAlonzo.Code.FlagshipFull.d_maxP_20 (coe v0))
                                 (coe
                                    MAlonzo.Code.Seed.du_drawAt_14 (coe v1)
                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("  ask=" :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (MAlonzo.Code.Data.Rational.Show.d_show_6
                                    (coe
                                       MAlonzo.Code.L0AgentStrategy.d_l0Tick_6 (coe (3 :: Integer))
                                       (coe MAlonzo.Code.FlagshipFull.d_maxP_20 (coe v0))
                                       (coe
                                          MAlonzo.Code.Seed.du_drawAt_14 (coe v1)
                                          (coe
                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("  L0=" :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       (MAlonzo.Code.Data.Rational.Show.d_show_6
                                          (coe
                                             MAlonzo.Code.SimulationModel.d_l0RealizedSurplus_22
                                             (coe
                                                MAlonzo.Code.L0AgentStrategy.d_concreteL0Sim_90
                                                (3 :: Integer) v0 v1)))
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("  L3=" :: Data.Text.Text)
                                          (MAlonzo.Code.Data.Rational.Show.d_show_6
                                             (coe
                                                MAlonzo.Code.Trace.d_realizedSurplus_30
                                                (coe
                                                   MAlonzo.Code.FlagshipFull.d_concreteSim_76
                                                   (coe (3 :: Integer)) (coe v0)
                                                   (coe v1))))))))))))))))
-- Main.printAll
d_printAll_44 ::
  MAlonzo.Code.FlagshipFull.T_SimEnvironment_2 ->
  [MAlonzo.Code.Data.Vec.Base.T_Vec_28] ->
  MAlonzo.Code.IO.Base.T_IO_20
d_printAll_44 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.IO.Base.C_pure_30
             (coe MAlonzo.Code.Data.Unit.Polymorphic.Base.du_tt_16)
      (:) v2 v3
        -> coe
             MAlonzo.Code.IO.Base.du__'62''62'__114
             (coe d_simRow_24 (coe v0) (coe v2))
             (coe d_printAll_44 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Main.program
d_program_52 :: MAlonzo.Code.IO.Base.T_IO_20
d_program_52
  = coe
      MAlonzo.Code.IO.Base.du__'62''62'__114
      (coe
         MAlonzo.Code.IO.Base.du__'62''62'__114
         (coe
            MAlonzo.Code.IO.Base.du__'62''62'__114
            (coe
               MAlonzo.Code.IO.Base.du__'62''62'__114
               (coe
                  MAlonzo.Code.IO.Base.du__'62''62'__114
                  (coe
                     MAlonzo.Code.IO.Base.du__'62''62'__114
                     (coe
                        MAlonzo.Code.IO.Base.du__'62''62'__114
                        (coe
                           MAlonzo.Code.IO.Base.du__'62''62'__114
                           (coe
                              MAlonzo.Code.IO.Base.du__'62''62'__114
                              (coe
                                 MAlonzo.Code.IO.Base.du__'62''62'__114
                                 (coe
                                    MAlonzo.Code.IO.Base.du__'62''62'__114
                                    (coe
                                       MAlonzo.Code.IO.Base.du__'62''62'__114
                                       (coe
                                          MAlonzo.Code.IO.Base.du__'62''62'__114
                                          (coe
                                             MAlonzo.Code.IO.Base.du__'62''62'__114
                                             (coe
                                                MAlonzo.Code.IO.Base.du__'62''62'__114
                                                (coe
                                                   MAlonzo.Code.IO.Base.du__'62''62'__114
                                                   (coe
                                                      MAlonzo.Code.IO.Finite.d_putStrLn_28
                                                      (coe MAlonzo.Code.Level.d_0ℓ_22)
                                                      (coe
                                                         ("=== Environment 1: witness (v_buyer=1, v_seller=2, maxP=3) ==="
                                                          ::
                                                          Data.Text.Text)))
                                                   (coe
                                                      MAlonzo.Code.IO.Finite.d_putStrLn_28
                                                      (coe MAlonzo.Code.Level.d_0ℓ_22)
                                                      (coe
                                                         ("  L0 bid/ask from full grid {0, 3/4, 3/2, 9/4}"
                                                          ::
                                                          Data.Text.Text))))
                                                (coe
                                                   MAlonzo.Code.IO.Finite.d_putStrLn_28
                                                   (coe MAlonzo.Code.Level.d_0ℓ_22)
                                                   (coe
                                                      ("  L3 buyer bids in {0, 1/4, 1/2, 3/4}  (cap at v=1)"
                                                       ::
                                                       Data.Text.Text))))
                                             (coe
                                                MAlonzo.Code.IO.Finite.d_putStrLn_28
                                                (coe MAlonzo.Code.Level.d_0ℓ_22)
                                                (coe
                                                   ("  L3 seller asks in {2, 9/4, 5/2, 11/4} (floor at v=2)"
                                                    ::
                                                    Data.Text.Text))))
                                          (coe
                                             MAlonzo.Code.IO.Finite.d_putStrLn_28
                                             (coe MAlonzo.Code.Level.d_0ℓ_22)
                                             (coe
                                                ("  Result: L3 never trades; L0 trades and destroys value"
                                                 ::
                                                 Data.Text.Text))))
                                       (coe
                                          MAlonzo.Code.IO.Finite.d_putStrLn_28
                                          (coe MAlonzo.Code.Level.d_0ℓ_22)
                                          (coe ("" :: Data.Text.Text))))
                                    (coe
                                       MAlonzo.Code.IO.Finite.d_putStrLn_28
                                       (coe MAlonzo.Code.Level.d_0ℓ_22)
                                       (coe
                                          ("  seed  bid     ask     L0       L3"
                                           ::
                                           Data.Text.Text))))
                                 (coe
                                    d_printAll_44
                                    (coe MAlonzo.Code.L0AgentStrategy.d_witnessEnv_100)
                                    (coe d_allSeeds4_22)))
                              (coe
                                 MAlonzo.Code.IO.Finite.d_putStrLn_28
                                 (coe MAlonzo.Code.Level.d_0ℓ_22) (coe ("" :: Data.Text.Text))))
                           (coe
                              MAlonzo.Code.IO.Finite.d_putStrLn_28
                              (coe MAlonzo.Code.Level.d_0ℓ_22)
                              (coe
                                 ("=== Environment 2: market (v_buyer=3, v_seller=1, maxP=4) ==="
                                  ::
                                  Data.Text.Text))))
                        (coe
                           MAlonzo.Code.IO.Finite.d_putStrLn_28
                           (coe MAlonzo.Code.Level.d_0ℓ_22)
                           (coe
                              ("  L0 bid/ask from full grid {0, 1, 2, 3}" :: Data.Text.Text))))
                     (coe
                        MAlonzo.Code.IO.Finite.d_putStrLn_28
                        (coe MAlonzo.Code.Level.d_0ℓ_22)
                        (coe
                           ("  L3 buyer bids in {0, 3/4, 3/2, 9/4}    (cap at v=3)"
                            ::
                            Data.Text.Text))))
                  (coe
                     MAlonzo.Code.IO.Finite.d_putStrLn_28
                     (coe MAlonzo.Code.Level.d_0ℓ_22)
                     (coe
                        ("  L3 seller asks in {1, 7/4, 5/2, 13/4}  (floor at v=1)"
                         ::
                         Data.Text.Text))))
               (coe
                  MAlonzo.Code.IO.Finite.d_putStrLn_28
                  (coe MAlonzo.Code.Level.d_0ℓ_22)
                  (coe
                     ("  Result: L3 trades at 3/16 seeds; L0 trades at 10/16 seeds"
                      ::
                      Data.Text.Text))))
            (coe
               MAlonzo.Code.IO.Finite.d_putStrLn_28
               (coe MAlonzo.Code.Level.d_0ℓ_22) (coe ("" :: Data.Text.Text))))
         (coe
            MAlonzo.Code.IO.Finite.d_putStrLn_28
            (coe MAlonzo.Code.Level.d_0ℓ_22)
            (coe ("  seed  bid     ask     L0       L3" :: Data.Text.Text))))
      (coe d_printAll_44 (coe d_marketEnv_12) (coe d_allSeeds4_22))
main = coe d_main_54
-- Main.main
d_main_54 ::
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    AgdaAny MAlonzo.Code.Level.T_Lift_8
d_main_54
  = coe
      MAlonzo.Code.IO.Base.du_run_122 (coe MAlonzo.Code.Level.d_0ℓ_22)
      (coe d_program_52)
