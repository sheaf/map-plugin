{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections   #-}

module MapPlugin ( plugin ) where

-- base
import Control.Arrow
    ( (***) )
import Control.Monad
    ( join )
import Data.Either
    ( partitionEithers )
import Data.Foldable
    ( toList )
import Data.Maybe
    ( catMaybes, mapMaybe, maybeToList )
import Data.Traversable
    ( for )

-- containers
import Data.Map.Strict
    ( Map )
import qualified Data.Map.Strict
  as Map
    ( fromList, mapMaybeWithKey )

-- ghc
import qualified GHC
    ( Module, mkModuleName )
import qualified GHC.Builtin.Types
  as GHC
    ( promotedNothingDataCon, promotedJustDataCon )
import qualified GHC.Core
  as GHC
    ( Expr(Coercion) )
import qualified GHC.Core.Coercion
  as GHC
    ( Coercion, mkUnivCo, mkPrimEqPredRole )
{-
import qualified GHC.Core.DataCon
  as GHC
    ( promoteDataCon )
-}
import qualified GHC.Core.Predicate
  as GHC
    ( Pred(..), classifyPredType
    , EqRel(..)
    )
import qualified GHC.Core.TyCo.Rep
  as GHC
    ( Type(..)
    , UnivCoProvenance(..)
    )
import qualified GHC.Core.Type
  as GHC
    ( mkTyConApp )
import qualified GHC.Core.Unify
  as GHC
    ( tcMatchTy, typesCantMatch )
import qualified GHC.Driver.Finder
  as GHC
    ( FindResult(..) )
import qualified GHC.Data.FastString
  as GHC
    ( fsLit )
import qualified GHC.Plugins
  as GHC
    ( Plugin(..), defaultPlugin, purePlugin )
import qualified GHC.Core.DataCon
  as GHC
    ( DataCon )
import qualified GHC.Core.TyCon
  as GHC
    ( TyCon(..) )
import qualified GHC.Tc.Plugin
  as GHC
    ( findImportedModule
    , lookupOrig, tcLookupTyCon, tcLookupDataCon
    , newGiven
    )
import qualified GHC.Tc.Types
  as GHC
    ( TcPlugin(..)
    , TcPluginM
    , TcPluginResult(..)
    )
import qualified GHC.Tc.Types.Constraint
  as GHC
    ( Ct(..), ctPred, ctLoc
    , bumpCtLocDepth, mkNonCanonical
    )
import qualified GHC.Tc.Types.Evidence
  as GHC
    ( EvTerm, Role(..) )
import qualified GHC.Types.Name.Occurrence
  as GHC
    ( mkDataOcc, mkTcOcc )
import qualified GHC.Types.Var
  as GHC
    ( TcTyVar )
import qualified GHC.Utils.Outputable
  as GHC
    ( ppr, pprTrace ) --, pprPanic )

--------------------------------------------------------------------------------
-- Plugin definition and setup/finalisation.

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.tcPlugin        = tcPlugin
    , GHC.pluginRecompile = GHC.purePlugin
    }

tcPlugin :: [ String ] -> Maybe GHC.TcPlugin
tcPlugin _args =
  Just $
    GHC.TcPlugin
      { GHC.tcPluginInit  = tcPluginInit
      , GHC.tcPluginSolve = tcPluginSolve
      , GHC.tcPluginStop  = tcPluginStop
      }

data PluginDefs =
  PluginDefs
    { keyValTyCon     :: !GHC.TyCon
    , keyValDataCon   :: !GHC.DataCon
    , mapTyCon        :: !GHC.TyCon
    , fromListDataCon :: !GHC.DataCon
    , lookupTyCon     :: !GHC.TyCon
    , insertTyCon     :: !GHC.TyCon
    , deleteTyCon     :: !GHC.TyCon
    , unionTyCon      :: !GHC.TyCon
    , differenceTyCon :: !GHC.TyCon
    }

findModule :: String -> String -> GHC.TcPluginM GHC.Module
findModule pkg modName = do
  findResult <- GHC.findImportedModule ( GHC.mkModuleName modName ) ( Just $ GHC.fsLit pkg )
  case findResult of
    GHC.Found _ res     -> pure res
    GHC.FoundMultiple _ -> error $ "MapPlugin: found multiple modules named " <> modName <> "."
    _                   -> error $ "MapPlugin: could not find any module named " <> modName <> "."

tcPluginInit :: GHC.TcPluginM PluginDefs
tcPluginInit = do
  dataTypeMapModule <- findModule "Map-Plugin" "Data.Type.Map"
  keyValTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   ":->"        )
  keyValDataCon   <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkDataOcc ":->"        )
  mapTyCon        <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Map"        )
  fromListDataCon <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkDataOcc "FromList"   )
  lookupTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Lookup"     )
  insertTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Insert"     )
  deleteTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Delete"     )
  unionTyCon      <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Union"      )
  differenceTyCon <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Difference" )
  pure ( PluginDefs { .. } )

tcPluginStop :: PluginDefs -> GHC.TcPluginM ()
tcPluginStop _ = pure ()

--------------------------------------------------------------------------------
-- Looking through types and given constraints,
-- in order to find type family applications we're interested in.

data MapTyConApp
  = Lookup !GHC.Type !GHC.Type !GHC.Type !GHC.Type
  | Insert !GHC.Type !GHC.Type !GHC.Type !GHC.Type !GHC.Type
  | Delete !GHC.Type !GHC.Type !GHC.Type !GHC.Type
  -- others: todo

type FSk = GHC.TcTyVar

-- | Recognise fully saturated applications of supported types,
-- such as @ Insert {kind_k} {kind_v} k v m @.
recogniseExplicitMapTyConApp :: PluginDefs -> GHC.TyCon -> [ GHC.Type ] -> Maybe MapTyConApp
recogniseExplicitMapTyConApp ( PluginDefs { .. } ) tyCon args
  | tyCon == lookupTyCon
  , [ kind_k, kind_v, k, m ] <- args
  = Just $ Lookup kind_k kind_v k m
  | tyCon == insertTyCon
  , [ kind_k, kind_v, k, v, m ] <- args
  = Just $ Insert kind_k kind_v k v m
  | tyCon == deleteTyCon
  , [ kind_k, kind_v, k, m ] <- args
  = Just $ Delete kind_k kind_v k m
  | otherwise
  = Nothing

-- | Recognise supported types, either directly or through flattening skolem type variables.
recogniseMapTyConApp :: PluginDefs -> Map FSk MapTyConApp -> GHC.Type -> [ MapTyConApp ]
recogniseMapTyConApp pluginDefs fsks ty = case ty of
  GHC.TyConApp tyCon args -> maybeToList $ recogniseExplicitMapTyConApp pluginDefs tyCon args
  _ -> toList $ ( `Map.mapMaybeWithKey` fsks ) \ fsk tyConApp ->
        case GHC.tcMatchTy ty ( GHC.TyVarTy fsk ) of
          Nothing -> Nothing
          Just _  -> Just tyConApp

-- | Recognise supported type family applications in the provided list of given constraints.
relevantGivenFunEqs :: PluginDefs -> [ GHC.Ct ] -> Map FSk MapTyConApp
relevantGivenFunEqs pluginDefs = Map.fromList . mapMaybe \case
  GHC.CFunEqCan { cc_fun, cc_tyargs, cc_fsk }
    -> ( cc_fsk, ) <$> recogniseExplicitMapTyConApp pluginDefs cc_fun cc_tyargs
  _ -> Nothing

--------------------------------------------------------------------------------
-- Simplification of type family applications.

-- | Try to simplify a type, e.g. simplify @ Lookup k ( Insert k v s ) @ to @ v @.
simplify :: PluginDefs -> [ GHC.Ct ] -> Map FSk MapTyConApp -> GHC.Ct -> GHC.Type -> GHC.TcPluginM [ GHC.Ct ]
simplify pluginDefs _givens fsks wanted ty = do
  concat <$> for ( recogniseMapTyConApp pluginDefs fsks ty ) \case
    Lookup kind_k kind_v k kvs
      -> do
        simpls <- simplifyLookup pluginDefs fsks k kvs
        traverse 
          ( newDeducedGivenEq wanted ty )
          ( lookupSimplificationTy pluginDefs kind_k kind_v k <$> simpls )
    _ -> pure []

-- | Outcome of attempting to simplify a type family application `F ... a`.
data TyFamAppSimplification arg res
  = SimplifyArg arg   -- ^ Simplification of the last type family argument.
  | Result      res   -- ^ Computation of the full type family application.

-- | Tries to simplify a type family application @ Lookup k kvs @.
simplifyLookup :: PluginDefs -> Map FSk MapTyConApp -> GHC.Type -> GHC.Type
               -> GHC.TcPluginM [ TyFamAppSimplification GHC.Type ( Maybe GHC.Type ) ]
simplifyLookup pluginDefs fsks k0 kvs0 =
  catMaybes <$> for ( recogniseMapTyConApp pluginDefs fsks kvs0 ) \case
    Insert _kind_k _kind_v k1 v1 kvs1 -> do
      mbEq <- eqTy pluginDefs k0 k1
      case mbEq of
        -- @ Lookup k0 ( Insert k1 v1 kvs1 ) ~ Just v1 @ when @ k0 ~ k1 @.
        Just True  -> pure $ Just ( Result $ Just v1 )
        -- @ Lookup k0 ( Insert k1 v1 kvs1 ) ~ Lookup k0 kvs1 @ when @ k0 /~ k1 @.
        Just False -> pure $ Just ( SimplifyArg kvs1 )
        Nothing    -> pure Nothing
    Delete _kind_k _kind_v k1 kvs1 -> do
      mbEq <- eqTy pluginDefs k0 k1
      case mbEq of
        -- @ Lookup k0 ( Delete k1 kvs1 ) ~ Nothing @ when @ k0 ~ k1 @.
        Just True  -> pure $ Just ( Result Nothing )
        -- @ Lookup k0 ( Delete k1 kvs1 ) ~ Lookup k0 kvs1 @ when @ k0 /~ k1 @.
        Just False -> pure $ Just ( SimplifyArg kvs1 )
        -- If we don't know whether @ k0 @ and @ k1 @ can unify,
        -- it is still worth trying to simplify @ kvs1 @, as @ Lookup k0 kvs1 ~ Nothing @
        -- would also imply that @ Lookup k0 ( Delete k1 kvs1 ) ~ Nothing @.
        Nothing    -> do
          simplFurther <- simplifyLookup pluginDefs fsks k0 kvs1
          if any ( \case { Result Nothing -> True; _ -> False } ) simplFurther
          then pure $ Just ( Result Nothing )
          else pure Nothing
    _ -> pure Nothing

-- | Returns the type corresponding to the outcome of simplifying
-- an expression of the form @ Lookup k m @.
lookupSimplificationTy :: PluginDefs -> GHC.Type -> GHC.Type -> GHC.Type
                       -> TyFamAppSimplification GHC.Type ( Maybe GHC.Type )
                       -> GHC.Type
lookupSimplificationTy ( PluginDefs { lookupTyCon } ) kind_k kind_v k simpl = case simpl of
  SimplifyArg arg     -> GHC.mkTyConApp lookupTyCon [ kind_k, kind_v, k, arg ]
  Result ( Just res ) -> GHC.mkTyConApp GHC.promotedJustDataCon [ kind_v, res ]
  Result Nothing      -> GHC.mkTyConApp GHC.promotedNothingDataCon [ kind_v ]

--------------------------------------------------------------------------------
-- Handling equalities.

-- | Returns a new given equality constraint @ lhs ~ rhs @,
-- obtained by bumping the depth of the provided constraint.
newDeducedGivenEq :: GHC.Ct -> GHC.Type -> GHC.Type -> GHC.TcPluginM GHC.Ct
newDeducedGivenEq ct lhs rhs = do
  let
    coercion :: GHC.Coercion
    coercion = GHC.mkUnivCo ( GHC.PluginProv "Map-Plugin") GHC.Nominal lhs rhs
  evidence <-
    GHC.newGiven
      ( GHC.bumpCtLocDepth $ GHC.ctLoc ct )
      ( GHC.mkPrimEqPredRole GHC.Nominal lhs rhs )
      ( GHC.Coercion coercion )
  pure ( GHC.mkNonCanonical evidence )

-- | Computes whether `lhs == rhs`.
--
--  - @ Just True @: types are equal,
--  - @ Just False @: types are apart,
--  - @ Nothing @: unknown at this stage.
eqTy :: PluginDefs -> GHC.Type -> GHC.Type -> GHC.TcPluginM ( Maybe Bool )
eqTy ( PluginDefs {} ) lhs rhs
  | Just _ <- GHC.tcMatchTy lhs rhs
  = pure $ Just True
  | GHC.typesCantMatch [ ( lhs, rhs ) ]
  = pure $ Just False
  | otherwise
  = pure $ Nothing

--------------------------------------------------------------------------------
-- Solver part of the plugin.

tcPluginSolve :: PluginDefs -> [ GHC.Ct ] -> [ GHC.Ct ] -> [ GHC.Ct ] -> GHC.TcPluginM GHC.TcPluginResult
tcPluginSolve _defs _givens _deriveds []      = pure $ GHC.TcPluginOk [] []
tcPluginSolve  defs  givens  deriveds wanteds = do
  let
    fsks :: Map FSk MapTyConApp 
    fsks = GHC.pprTrace "Givens:"   ( GHC.ppr givens   )
         . GHC.pprTrace "Deriveds:" ( GHC.ppr deriveds )
         . GHC.pprTrace "Wanteds:"  ( GHC.ppr wanteds  )
         $ relevantGivenFunEqs defs givens
  ( contras, oks )
    <- partitionEithers
    <$> traverse ( \ wanted -> specifyWanted wanted <$> solveWanted defs givens fsks deriveds wanted ) wanteds
  case contras of
    [] ->
      let
        solveds :: [ ( GHC.EvTerm, GHC.Ct ) ]
        news    :: [ GHC.Ct ]
        ( solveds, news ) = ( catMaybes *** join ) ( unzip oks )
      in  pure $ GHC.TcPluginOk
                  ( GHC.pprTrace "Solveds:" ( GHC.ppr solveds ) $ solveds )
                  ( GHC.pprTrace "News:"    ( GHC.ppr news    ) $ news    )
    _  -> pure $ GHC.TcPluginContradiction contras

-- | Outcome of running the Map plugin on a single wanted constraint.
data SolverResult
  = Unsolved -- ^ Wanted constraint was not solved, but new constraints might be emitted.
    { newCts   :: ![ GHC.Ct ] }
  | Solved   -- ^ Wanted constraint has been solved: evidence, and new constraints to emit.
    { evidence :: !GHC.EvTerm
    , newCts   :: ![ GHC.Ct ]
    }
  | Contradiction -- ^ The plugin has uncovered a contradiction.

pattern Ignore :: SolverResult
pattern Ignore = Unsolved []

-- | Try to solve a wanted constraint.
--
-- This function currently never directly solves the constraint,
-- but might make progress (emitting new given constraints),
-- which hopefully will allow GHC to solve it.
solveWanted :: PluginDefs -> [ GHC.Ct ] -> Map FSk MapTyConApp  -> [ GHC.Ct ] -> GHC.Ct -> GHC.TcPluginM SolverResult
solveWanted pluginDefs givens fsks _deriveds wanted =
  case GHC.classifyPredType ( GHC.ctPred wanted ) of
    GHC.EqPred GHC.NomEq lhs rhs -> do
      newCts <- GHC.pprTrace "lhs =" ( GHC.ppr $ lhs )
              . GHC.pprTrace "rhs =" ( GHC.ppr $ rhs )
              $
              concat <$> traverse ( simplify pluginDefs givens fsks wanted ) [ lhs, rhs ]
      pure $ Unsolved {..}
    _ -> pure Ignore

-- | Passthrough of the wanted constraint, to report a solution/contradiction.
specifyWanted :: GHC.Ct -> SolverResult -> Either GHC.Ct ( Maybe ( GHC.EvTerm, GHC.Ct ), [ GHC.Ct ] )
specifyWanted _      ( Unsolved {..} ) = Right ( Nothing, newCts )
specifyWanted wanted ( Solved   {..} ) = Right ( Just ( evidence, wanted ), newCts )
specifyWanted wanted Contradiction     = Left wanted
