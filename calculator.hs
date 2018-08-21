{-# LANGUAGE OverloadedStrings #-}

module Main where

import Haste
import Haste.App
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Haste.Prim
import Data.Time (UTCTime (..), addUTCTime, defaultTimeLocale, diffUTCTime,
                  formatTime, fromGregorian, iso8601DateFormat, parseTimeM)
import Data.Time.Clock.POSIX (posixSecondsToUTCTime, utcTimeToPOSIXSeconds)


main = withElems ["dt","epoch","slot","k","ts"] calculator

calculator :: (MonadIO m, MonadEvent m, IsElem el) => [el] -> m ()
calculator [dt,epoch,slot,k,timestamp] = do
    --onEvent k     KeyUp $ \_ -> recalculateAll
    onEvent slot  KeyUp $ \_ -> recalculateTime
    onEvent epoch KeyUp $ \_ -> recalculateTime
    onEvent dt    KeyUp $ \_ -> recalculateBlock
    onEvent timestamp KeyUp $ \_ -> recalculateFromTime
    return ()
  where
    recalculateAll =
      recalculateTime  -- >> recalculateBlock

    hsFormatTime :: UTCTime -> String
    hsFormatTime = formatTime defaultTimeLocale (iso8601DateFormat (Just "%H:%M:%S"))
                           -- posixSecondsToUTCTime $ fromIntegral secs

    hsUTCTime :: String -> Maybe UTCTime
    hsUTCTime str = do
      parseTimeM True defaultTimeLocale (iso8601DateFormat (Just "%H:%M:%S")) str

    hsConvertTime :: String -> Maybe Integer
    hsConvertTime str = do
      fmap (round . utcTimeToPOSIXSeconds) $ parseTimeM True defaultTimeLocale (iso8601DateFormat (Just "%H:%M:%S")) str

    recalculateFromTime = do
      vt <- getValue timestamp
      vk <- getValue k
      case (vt, str2int vk) of
        (Just t', Just k') -> do
            case hsUTCTime t' of
              Just utc -> do
                  setProp epoch "value" (show $ calcEpoch utc k')
                  setProp slot "value" (show $ calcSlot utc k')
                  setProp dt "value" (show $ round $ utcTimeToPOSIXSeconds utc)
              Nothing    -> return ()
        _                  -> return ()

    --recalculateBlock :: MonadEvent m => m ()
    recalculateBlock = do
      vt <- getValue dt
      vk <- getValue k
      case (str2int vt, str2int vk) of
        (Just ti', Just k') -> do
            let t' = posixSecondsToUTCTime $ fromIntegral ti'
            if t' >= t0 then do
                setProp epoch "value" (show $ calcEpoch t' k')
                setProp slot "value" (show $ calcSlot t' k')
            else
                return ()
        _                  -> return ()

    --recalculateTime :: MonadEvent m => m ()
    recalculateTime = do
      vs <- getValue slot
      ve <- getValue epoch
      vk <- getValue k
      case (str2int vs, str2int ve, str2int vk) of
        (Just s', Just e', Just k') -> do
            newt <- return $ calcTime s' e' k'
            setProp dt "value" (show $ round $ utcTimeToPOSIXSeconds newt)
            newtstr <- return $ hsFormatTime newt
            --writeLog $ newtstr
            setProp timestamp "value" newtstr
        _                           -> return ()

    calcSlot :: UTCTime -> Integer -> Integer
    calcSlot t' k' = (diffSeconds t') `rem` (k' * ts * 10) `div` ts

    calcEpoch :: UTCTime -> Integer -> Integer
    calcEpoch t' k' = (diffSeconds t') `div` (k' * ts * 10)

    calcTime :: Integer -> Integer -> Integer -> UTCTime
    calcTime s' e' k' = addSeconds $ ts * (s' + e' * k' * 10)

    addSeconds :: Integer -> UTCTime
    addSeconds s = addUTCTime (fromIntegral s) t0

    diffSeconds :: UTCTime -> Integer
    diffSeconds utc = round $ diffUTCTime utc t0

    t0 :: UTCTime
    -- 2017-09-23 21:44:51 UTC
    t0 = UTCTime (fromGregorian 2017 9 23) (fromIntegral $ 21*3600 + 44*60 + 51)

    ts :: Integer
    ts = 20   -- seconds per block


str2int :: Maybe String -> Maybe Integer
str2int Nothing = Nothing
str2int (Just v) = Just d
  where
    d = read v :: Integer

