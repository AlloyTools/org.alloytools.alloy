tell application "Finder"
  tell disk "Alloy"
    open
    set current view of container window to icon view
    set toolbar visible of container window to false
    set statusbar visible of container window to false

    -- size of window should match size of background
    set the bounds of container window to {400, 100, 917, 370}

    set theViewOptions to the icon view options of container window
    set arrangement of theViewOptions to not arranged
    set icon size of theViewOptions to 128
    set background picture of theViewOptions to file ".background:background.png"

    -- Create alias for install location
    make new alias file at container window to POSIX file "/Applications" with properties {name:"Applications"}

    -- First, move all files far enough to be not visible if user has "show hidden files" option set
    -- Note: this only make sense if "hidden" files are also visible on the build system
    --   otherwise command below will only return list of non-hidden items
    set filesToHide to the name of every item of container window
    repeat with theFile in filesToHide
         set position of item theFile of container window to {1000, 0}
    end repeat

    -- Now position application and install location
    set position of item "Alloy" of container window to {120, 135}
    set position of item "Applications" of container window to {390, 135}

    close
    open
    update without registering applications
    delay 5
  end tell
end tell

