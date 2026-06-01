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

module MAlonzo.Code.Flagship where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agent
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Proposal
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Trace

-- Flagship.2ℚ
d_2ℚ_2 :: MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_2ℚ_2
  = coe
      MAlonzo.Code.Data.Rational.Base.du__'47'__156 (coe (2 :: Integer))
      (coe (1 :: Integer))
-- Flagship.3ℚ
d_3ℚ_4 :: MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_3ℚ_4
  = coe
      MAlonzo.Code.Data.Rational.Base.du__'47'__156 (coe (3 :: Integer))
      (coe (1 :: Integer))
-- Flagship.RawMatch
d_RawMatch_6 = ()
data T_RawMatch_6
  = C_constructor_36 MAlonzo.Code.Agent.T_Agent_18
                     MAlonzo.Code.Agent.T_Agent_18 MAlonzo.Code.Proposal.T_Proposal_2
                     MAlonzo.Code.Proposal.T_Proposal_2
                     MAlonzo.Code.Data.Rational.Base.T__'8804'__54
                     MAlonzo.Code.Data.Rational.Base.T_ℚ_6
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Flagship.RawMatch.buyer
d_buyer_22 :: T_RawMatch_6 -> MAlonzo.Code.Agent.T_Agent_18
d_buyer_22 v0
  = case coe v0 of
      C_constructor_36 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Flagship.RawMatch.seller
d_seller_24 :: T_RawMatch_6 -> MAlonzo.Code.Agent.T_Agent_18
d_seller_24 v0
  = case coe v0 of
      C_constructor_36 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Flagship.RawMatch.bid
d_bid_26 :: T_RawMatch_6 -> MAlonzo.Code.Proposal.T_Proposal_2
d_bid_26 v0
  = case coe v0 of
      C_constructor_36 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Flagship.RawMatch.ask
d_ask_28 :: T_RawMatch_6 -> MAlonzo.Code.Proposal.T_Proposal_2
d_ask_28 v0
  = case coe v0 of
      C_constructor_36 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Flagship.RawMatch.crosses
d_crosses_30 ::
  T_RawMatch_6 -> MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_crosses_30 v0
  = case coe v0 of
      C_constructor_36 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Flagship.RawMatch.clearingPrice
d_clearingPrice_32 ::
  T_RawMatch_6 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_clearingPrice_32 v0
  = case coe v0 of
      C_constructor_36 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Flagship.RawMatch.priceInRange
d_priceInRange_34 ::
  T_RawMatch_6 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_priceInRange_34 v0
  = case coe v0 of
      C_constructor_36 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Flagship.rawSurplus
d_rawSurplus_38 ::
  T_RawMatch_6 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_rawSurplus_38 v0
  = coe
      MAlonzo.Code.Data.Rational.Base.d__'45'__282
      (coe
         MAlonzo.Code.Agent.d_unitValue_12
         (coe MAlonzo.Code.Agent.d_valuation_34 (coe d_buyer_22 (coe v0))))
      (coe
         MAlonzo.Code.Agent.d_unitValue_12
         (coe MAlonzo.Code.Agent.d_valuation_34 (coe d_seller_24 (coe v0))))
-- Flagship.buyerWitness
d_buyerWitness_42 :: MAlonzo.Code.Agent.T_Agent_18
d_buyerWitness_42
  = coe
      MAlonzo.Code.Agent.C_constructor_40 (coe (0 :: Integer))
      (coe MAlonzo.Code.Agent.C_Buyer_4)
      (coe
         MAlonzo.Code.Agent.C_constructor_14
         (coe MAlonzo.Code.Data.Rational.Base.d_1ℚ_180))
      (coe d_3ℚ_4) (coe (0 :: Integer))
-- Flagship.sellerWitness
d_sellerWitness_44 :: MAlonzo.Code.Agent.T_Agent_18
d_sellerWitness_44
  = coe
      MAlonzo.Code.Agent.C_constructor_40 (coe (1 :: Integer))
      (coe MAlonzo.Code.Agent.C_Seller_6)
      (coe MAlonzo.Code.Agent.C_constructor_14 (coe d_2ℚ_2))
      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe (1 :: Integer))
-- Flagship.bidWitness
d_bidWitness_46 :: MAlonzo.Code.Proposal.T_Proposal_2
d_bidWitness_46
  = coe
      MAlonzo.Code.Proposal.C_constructor_16 (coe (0 :: Integer))
      (coe d_3ℚ_4) (coe MAlonzo.Code.Agent.C_Buyer_4)
-- Flagship.askWitness
d_askWitness_48 :: MAlonzo.Code.Proposal.T_Proposal_2
d_askWitness_48
  = coe
      MAlonzo.Code.Proposal.C_constructor_16 (coe (1 :: Integer))
      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
      (coe MAlonzo.Code.Agent.C_Seller_6)
-- Flagship.witnessMatch
d_witnessMatch_50 :: T_RawMatch_6
d_witnessMatch_50
  = coe
      C_constructor_36 (coe d_buyerWitness_42) (coe d_sellerWitness_44)
      (coe d_bidWitness_46) (coe d_askWitness_48)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
         (coe
            MAlonzo.Code.Data.Rational.Properties.d__'8804''63'__3622
            (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe d_3ℚ_4)))
      (coe MAlonzo.Code.Data.Rational.Base.d_1ℚ_180)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
            (coe
               MAlonzo.Code.Data.Rational.Properties.d__'8804''63'__3622
               (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
               (coe MAlonzo.Code.Data.Rational.Base.d_1ℚ_180)))
         (coe
            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
            (coe
               MAlonzo.Code.Data.Rational.Properties.d__'8804''63'__3622
               (coe MAlonzo.Code.Data.Rational.Base.d_1ℚ_180) (coe d_3ℚ_4))))
-- Flagship.witnessSellerHigher
d_witnessSellerHigher_52 ::
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_witnessSellerHigher_52
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_toWitness_144
      (coe
         MAlonzo.Code.Data.Rational.Properties.d__'60''63'__3804
         (coe MAlonzo.Code.Data.Rational.Base.d_1ℚ_180) (coe d_2ℚ_2))
-- Flagship.dominance
d_dominance_58 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dominance_58
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Trace.d_realizedSurplusNonNeg_60)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_witnessMatch_50)
         (coe d_witnessSellerHigher_52))
