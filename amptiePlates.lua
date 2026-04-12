-- amptiePlates — Lightweight enemy nameplate addon (TankPlates-style)
-- Vanilla WoW 1.12 / Lua 5.0 / TurtleWoW (SuperWoW required)
-- Modifies original Blizzard bars directly — no overlay StatusBars.

local getn    = table.getn
local tinsert = table.insert
local floor   = math.floor
local sfind   = string.find
local pairs   = pairs
local GetTime = GetTime
local UnitName = UnitName
local UnitExists = UnitExists

-- ============================================================
-- DB
-- ============================================================
AmptiePlatesDB = AmptiePlatesDB or {}

local function GetDB()
    local db = AmptiePlatesDB
    if db.barWidth   == nil then db.barWidth   = 120  end
    if db.barHeight  == nil then db.barHeight  = 10   end
    if db.cbHeight   == nil then db.cbHeight   = 7    end
    if db.mode       == nil then db.mode       = "dps" end
    if db.enabled    == nil then db.enabled    = true  end
    if db.clickThrough == nil then db.clickThrough = false end
    if db.overlap      == nil then db.overlap      = false end
    if not db.debuffWhitelist then db.debuffWhitelist = {} end
    if not db.buffWhitelist   then db.buffWhitelist   = {} end
    return db
end

-- ============================================================
-- Constants
-- ============================================================
local AP_HAS_SUPERWOW = (SpellInfo ~= nil)
local AP_HAS_LIBDEBUFF = false  -- set at login after pfUI loads
local AP_CAN_TRACK_AURAS = false
local AP_MAX_AURA_ICONS = 4

local AP_BACKDROP = {
    bgFile   = "Interface\\Buttons\\WHITE8X8",
    edgeFile = "Interface\\Buttons\\WHITE8X8",
    edgeSize = 2,
    insets   = { left = 0, right = 0, top = 0, bottom = 0 },
}

local AP_COLORS = {
    ENEMY_NPC    = { 0.90, 0.20, 0.30 },
    NEUTRAL_NPC  = { 1.00, 1.00, 0.30 },
}

local AP_CLASS_COLORS = {
    WARRIOR     = { 0.78, 0.61, 0.43 },
    PALADIN     = { 0.96, 0.55, 0.73 },
    HUNTER      = { 0.67, 0.83, 0.45 },
    ROGUE       = { 1.00, 0.96, 0.41 },
    PRIEST      = { 1.00, 1.00, 1.00 },
    SHAMAN      = { 0.00, 0.44, 0.87 },
    MAGE        = { 0.41, 0.80, 0.94 },
    WARLOCK     = { 0.58, 0.51, 0.79 },
    DRUID       = { 1.00, 0.49, 0.04 },
}

local AP_THREAT_GREEN  = { 0.20, 0.90, 0.30 }
local AP_THREAT_YELLOW = { 1.00, 0.85, 0.00 }
local AP_THREAT_ORANGE = { 0.85, 0.45, 0.10 }
local AP_THREAT_RED    = { 0.90, 0.20, 0.30 }
local AP_THREAT_GREY   = { 0.50, 0.50, 0.50 }
local AP_THRESH_LOW  = 60   -- green → yellow
local AP_THRESH_HIGH = 85   -- yellow → orange

-- ============================================================
-- Performance tiers (based on in-combat plate count)
-- ============================================================
-- thresholds: true = show yellow/orange gradations, false = only green/red/grey
-- aura: 0=off, 1=all plates, 2=dirty only (staggered), 3=own target only
local AP_TIERS = {
    { scan = 0.10, thresholds = true,  cbThrottle = 0,    levelCache = false, stagger = 0, share = 0.20, aura = 1 }, -- 1-4
    { scan = 0.20, thresholds = true,  cbThrottle = 0.03, levelCache = false, stagger = 0, share = 0.40, aura = 1 }, -- 5-8
    { scan = 0.30, thresholds = true,  cbThrottle = 0.05, levelCache = true,  stagger = 3, share = 0.60, aura = 2 }, -- 9-12
    { scan = 0.50, thresholds = false, cbThrottle = 0.08, levelCache = true,  stagger = 2, share = 1.00, aura = 3 }, -- 13-15
    { scan = 1.00, thresholds = false, cbThrottle = 0.10, levelCache = true,  stagger = 1, share = 1.50, aura = 0 }, -- 16+
}
local activeTier = AP_TIERS[1]
local combatPlateCount = 0

local function GetTier(count)
    if count <= 4  then return AP_TIERS[1] end
    if count <= 8  then return AP_TIERS[2] end
    if count <= 12 then return AP_TIERS[3] end
    if count <= 15 then return AP_TIERS[4] end
    return AP_TIERS[5]
end

-- ============================================================
-- State
-- ============================================================
local registry = {}   -- plate → plate data table
local playerGuid = nil

-- Per-GUID tracking (like TankPlates): target history + casting state
local tracked = {}  -- guid → { current_target, previous_target, casting, casting_at }

-- ============================================================
-- Helpers (must be defined before threat sharing)
-- ============================================================
local function AP_GetGuid(plate)
    if not AP_HAS_SUPERWOW then return nil end
    local guid = plate:GetName(1)
    if guid and guid ~= "" and guid ~= "0x0000000000000000" then return guid end
    return nil
end

local function IsMaintank(name)
    if not name or name == "" then return false end
    if not amptieRaidToolsDB then return false end
    local ra = amptieRaidToolsDB.raidAssists
    if not ra or not ra.mainTanks then return false end
    local mts = ra.mainTanks
    for i = 1, 8 do
        if mts[i] and mts[i] == name then return true end
    end
    return false
end

local function AP_HasTWThreat()
    return (_G.TWT ~= nil and _G.TWT.threats ~= nil)
end

local function AP_GetThreatInfo()
    if not AP_HasTWThreat() then return nil, nil, nil end
    local threats = TWT.threats
    local myName = UnitName("player")
    local aggroKey = TWT.AGRO or "-Pull Aggro at-"
    local myPerc = nil
    local iAmTank = false
    local highestNonMTPerc = 0
    for pName, data in pairs(threats) do
        if pName == myName then
            myPerc = data.perc
            iAmTank = data.tank
        end
        if not data.tank and pName ~= aggroKey and not IsMaintank(pName) then
            if data.perc and data.perc > highestNonMTPerc then
                highestNonMTPerc = data.perc
            end
        end
    end
    return highestNonMTPerc, myPerc, iAmTank
end

-- Crowd-sourced threat sharing
local AP_SharedThreats = {}  -- mobGuid → { [playerName]=perc, _tank=name, _time=GetTime() }
local AP_SHARE_PREFIX = "APT"
local AP_SHARE_STALE  = 3     -- seconds before shared data expires
local shareTimer = 0
local shareJitter = 0          -- computed at login from raid index

-- ============================================================
-- Threat sharing: send & receive
-- ============================================================
local function AP_GetChannel()
    if GetNumRaidMembers() > 0 then return "RAID" end
    if GetNumPartyMembers() > 0 then return "PARTY" end
    return nil
end

local function AP_ShareThreat()
    if not AP_HasTWThreat() then return end
    if not UnitExists("target") then return end
    if not UnitAffectingCombat("player") then return end
    if not UnitAffectingCombat("target") then return end

    local channel = AP_GetChannel()
    if not channel then return end

    local _, targetGuid = UnitExists("target")
    if not targetGuid or targetGuid == "" then return end

    local threats = TWT.threats
    local aggroKey = TWT.AGRO or "-Pull Aggro at-"

    -- Build compact message: mobGuid;tankName;player1:perc1;player2:perc2...
    local parts = { targetGuid }
    local tankName = TWT.tankName or ""
    tinsert(parts, tankName)

    local count = 0
    local msg = targetGuid .. ";" .. tankName
    for pName, data in pairs(threats) do
        if pName ~= aggroKey and data.perc then
            local entry = ";" .. pName .. ":" .. floor(data.perc)
            if string.len(msg) + string.len(entry) < 240 then
                msg = msg .. entry
                count = count + 1
            end
        end
    end

    if count > 0 then
        SendAddonMessage(AP_SHARE_PREFIX, msg, channel)
    end
end

local function AP_ReceiveThreat(msg)
    -- Parse: mobGuid;tankName;player1:perc1;player2:perc2...
    local entries = {}
    local n = 0
    for part in string.gfind(msg, "[^;]+") do
        n = n + 1
        entries[n] = part
    end

    if n < 3 then return end -- need at least guid + tank + 1 entry

    local mobGuid = entries[1]
    local tankName = entries[2]

    local data = AP_SharedThreats[mobGuid]
    if not data then
        data = {}
        AP_SharedThreats[mobGuid] = data
    end

    -- Clear old player entries (keep meta fields)
    for k in pairs(data) do
        if k ~= "_tank" and k ~= "_time" then
            data[k] = nil
        end
    end

    data._tank = tankName
    data._time = GetTime()

    for i = 3, n do
        local _, _, pName, perc = sfind(entries[i], "^(.+):([%d%.]+)$")
        if pName and perc then
            data[pName] = tonumber(perc)
        end
    end
end

-- ============================================================
-- Target tracking
-- ============================================================
local function AP_EnsureTracked(guid)
    if not tracked[guid] then
        tracked[guid] = {
            current_target = nil,
            previous_target = nil,
            casting = false,
            casting_at = nil,
        }
    end
    return tracked[guid]
end

-- Update a mob's current target, preserving previous
local function AP_UpdateTarget(guid)
    if not guid then return end
    local unit = AP_EnsureTracked(guid)
    local _, targetGuid = UnitExists(guid .. "target")
    if targetGuid ~= unit.current_target then
        if unit.current_target then
            unit.previous_target = unit.current_target
        end
        unit.current_target = targetGuid
    end
end

-- Get the "real" aggro target: if mob is casting, use previous_target
-- (mob may temporarily switch target for a spell)
local function AP_GetAggroTarget(guid)
    local unit = tracked[guid]
    if not unit then
        local _, targetGuid = UnitExists(guid .. "target")
        return targetGuid
    end
    if unit.casting then
        -- During a cast, use previous target (before cast started).
        -- Fall back to current if no previous exists (mob never switched target).
        return unit.previous_target or unit.current_target
    end
    return unit.current_target
end

-- Extract threat info from shared data for a specific mob GUID
local function AP_GetSharedThreatInfo(guid)
    local sdata = AP_SharedThreats[guid]
    if not sdata or not sdata._time then return nil, nil, nil end
    if (GetTime() - sdata._time) > AP_SHARE_STALE then return nil, nil, nil end

    local myName = UnitName("player")
    local myPerc = sdata[myName]
    local tankName = sdata._tank
    local iAmTank = (tankName == myName)
    local highestNonMTPerc = 0

    for pName, perc in pairs(sdata) do
        -- Skip meta fields and tank and maintanks
        if pName ~= "_tank" and pName ~= "_time" and pName ~= tankName and not IsMaintank(pName) then
            if perc and perc > highestNonMTPerc then
                highestNonMTPerc = perc
            end
        end
    end

    return highestNonMTPerc, myPerc, iAmTank, tankName
end

-- ============================================================
-- Aura scanning (feature-gated: pfUI.libdebuff or SuperWoW)
-- ============================================================
local auraGuidDirty = {}  -- guid → true (set by events, cleared after scan)

local function AP_ScanAuras(plate, pd, guid)
    if not AP_CAN_TRACK_AURAS or not guid then return end

    local db = GetDB()
    local debuffWL = db.debuffWhitelist
    local buffWL = db.buffWhitelist

    -- Check if any whitelist entries exist
    local hasWhitelist = false
    for _ in pairs(debuffWL) do hasWhitelist = true; break end
    if not hasWhitelist then
        for _ in pairs(buffWL) do hasWhitelist = true; break end
    end
    if not hasWhitelist then
        -- No whitelist entries → hide all icons
        for i = 1, AP_MAX_AURA_ICONS do
            if pd.auraIcons[i] then pd.auraIcons[i]:Hide() end
        end
        return
    end

    -- Tier check
    local auraMode = activeTier.aura
    if auraMode == 0 then
        for i = 1, AP_MAX_AURA_ICONS do
            if pd.auraIcons[i] then pd.auraIcons[i]:Hide() end
        end
        return
    end
    if auraMode == 2 and not auraGuidDirty[guid] then return end
    if auraMode == 3 then
        local isTarget = UnitExists("target") and UnitIsUnit("target", guid)
        if not isTarget then return end
    end
    auraGuidDirty[guid] = nil

    local iconIdx = 0

    -- Path A: pfUI.libdebuff (event-driven, most accurate)
    if AP_HAS_LIBDEBUFF then
        local libdebuff = pfUI.libdebuff
        -- Scan debuffs
        if libdebuff.IterDebuffs then
            libdebuff:IterDebuffs(guid, function(auraSlot, spellId, effect, texture, stacks, dtype, duration, timeleft)
                if not effect or iconIdx >= AP_MAX_AURA_ICONS then return end
                local wlVal = debuffWL[effect]
                if wlVal then
                    iconIdx = iconIdx + 1
                    local icon = pd.auraIcons[iconIdx]
                    icon.tex:SetTexture(type(wlVal) == "string" and wlVal or texture)
                    if stacks and stacks > 1 then
                        icon.count:SetText(stacks)
                        icon.count:Show()
                    else
                        icon.count:Hide()
                    end
                    icon:Show()
                end
            end)
        end
        -- Scan buffs via UnitBuff (libdebuff only tracks debuffs)
        if iconIdx < AP_MAX_AURA_ICONS then
            for bi = 1, 32 do
                if iconIdx >= AP_MAX_AURA_ICONS then break end
                local bTex, bStacks, _, bSpellId = UnitBuff(guid, bi)
                if not bTex then break end
                if bSpellId then
                    local spellName = SpellInfo(bSpellId)
                    local bWlVal = spellName and buffWL[spellName]
                    if bWlVal then
                        iconIdx = iconIdx + 1
                        local icon = pd.auraIcons[iconIdx]
                        icon.tex:SetTexture(type(bWlVal) == "string" and bWlVal or bTex)
                        if bStacks and bStacks > 1 then
                            icon.count:SetText(bStacks)
                            icon.count:Show()
                        else
                            icon.count:Hide()
                        end
                        icon:Show()
                    end
                end
            end
        end

    -- Path B: SuperWoW only (UnitDebuff/UnitBuff polling with GUID)
    elseif AP_HAS_SUPERWOW then
        -- Debuffs
        for di = 1, 64 do
            if iconIdx >= AP_MAX_AURA_ICONS then break end
            local dTex, dStacks, _, dSpellId = UnitDebuff(guid, di)
            if not dTex then break end
            if dSpellId then
                local spellName = SpellInfo(dSpellId)
                local dWlVal = spellName and debuffWL[spellName]
                if dWlVal then
                    iconIdx = iconIdx + 1
                    local icon = pd.auraIcons[iconIdx]
                    icon.tex:SetTexture(type(dWlVal) == "string" and dWlVal or dTex)
                    if dStacks and dStacks > 1 then
                        icon.count:SetText(dStacks)
                        icon.count:Show()
                    else
                        icon.count:Hide()
                    end
                    icon:Show()
                end
            end
        end
        -- Buffs
        for bi = 1, 32 do
            if iconIdx >= AP_MAX_AURA_ICONS then break end
            local bTex, bStacks, _, bSpellId = UnitBuff(guid, bi)
            if not bTex then break end
            if bSpellId then
                local spellName = SpellInfo(bSpellId)
                local bWlVal = spellName and buffWL[spellName]
                if bWlVal then
                    iconIdx = iconIdx + 1
                    local icon = pd.auraIcons[iconIdx]
                    icon.tex:SetTexture(type(bWlVal) == "string" and bWlVal or bTex)
                    if bStacks and bStacks > 1 then
                        icon.count:SetText(bStacks)
                        icon.count:Show()
                    else
                        icon.count:Hide()
                    end
                    icon:Show()
                end
            end
        end
    end

    -- Hide unused icons
    for i = iconIdx + 1, AP_MAX_AURA_ICONS do
        if pd.auraIcons[i] then pd.auraIcons[i]:Hide() end
    end
end

local function GetUnitType(r, g, b)
    if r > 0.5 and g < 0.5 then return "ENEMY_NPC" end
    if r > 0.5 and g > 0.5 and b < 0.5 then return "NEUTRAL_NPC" end
    return nil
end

-- ============================================================
-- Threat color logic
-- ============================================================
local function GetThreatColor(plate, guid, db)
    if not AP_HAS_SUPERWOW or not playerGuid or not guid then return nil end
    if not UnitAffectingCombat("player") then return nil end
    if not UnitAffectingCombat(guid) then return nil end

    -- Update target tracking (ignores temporary cast targets)
    AP_UpdateTarget(guid)
    local targetGuid = AP_GetAggroTarget(guid)
    local targeting_me = (targetGuid == playerGuid)

    -- Data sources (priority: TWT.threats > SharedThreats > tankModeThreats > target)
    local isCurrentTarget = UnitExists("target") and UnitIsUnit("target", guid)
    local highestNonMTPerc, myPerc, iAmTank, tankerName

    -- Source 1: TWT.threats (full detail, own target only)
    if isCurrentTarget and AP_HasTWThreat() then
        highestNonMTPerc, myPerc, iAmTank = AP_GetThreatInfo()
        tankerName = TWT.tankName
    end

    -- Source 2: SharedThreats (from other AmptiePlates users, any mob)
    if iAmTank == nil then
        local sHighest, sMyPerc, sIAmTank, sTanker = AP_GetSharedThreatInfo(guid)
        if sIAmTank ~= nil then
            if not highestNonMTPerc then highestNonMTPerc = sHighest end
            if not myPerc then myPerc = sMyPerc end
            iAmTank = sIAmTank
            if not tankerName then tankerName = sTanker end
        end
    end

    -- Source 3: tankModeThreats (per-GUID from TWThreat server)
    local tmData = AP_HasTWThreat() and TWT.tankModeThreats and TWT.tankModeThreats[guid]
    local myName = UnitName("player")

    if iAmTank == nil and tmData and tmData.name then
        iAmTank = (tmData.name == myName)
        if not tankerName then tankerName = tmData.name end
    end

    -- Source 4: SuperWoW target fallback
    if not tankerName and targetGuid and targetGuid ~= "" then
        tankerName = UnitName(targetGuid)
    end

    -- Final aggro determination
    local iHaveAggro = targeting_me
    if iAmTank ~= nil then iHaveAggro = iAmTank end

    local showThresholds = activeTier.thresholds

    if db.mode == "tank" then
        -- TANK MODE
        if not iHaveAggro then
            if tankerName and IsMaintank(tankerName) then
                return AP_THREAT_GREY[1], AP_THREAT_GREY[2], AP_THREAT_GREY[3]
            end
            return AP_THREAT_RED[1], AP_THREAT_RED[2], AP_THREAT_RED[3]
        end

        if showThresholds then
            local dangerPerc = highestNonMTPerc
            if not dangerPerc and tmData and tmData.perc then
                dangerPerc = tmData.perc
            end
            if dangerPerc then
                if dangerPerc >= AP_THRESH_HIGH then
                    return AP_THREAT_ORANGE[1], AP_THREAT_ORANGE[2], AP_THREAT_ORANGE[3]
                elseif dangerPerc >= AP_THRESH_LOW then
                    return AP_THREAT_YELLOW[1], AP_THREAT_YELLOW[2], AP_THREAT_YELLOW[3]
                end
            end
        end
        return AP_THREAT_GREEN[1], AP_THREAT_GREEN[2], AP_THREAT_GREEN[3]
    else
        -- DPS/HEALER MODE
        if iHaveAggro then
            return AP_THREAT_RED[1], AP_THREAT_RED[2], AP_THREAT_RED[3]
        end

        if showThresholds and myPerc then
            if myPerc >= AP_THRESH_HIGH then
                return AP_THREAT_ORANGE[1], AP_THREAT_ORANGE[2], AP_THREAT_ORANGE[3]
            elseif myPerc >= AP_THRESH_LOW then
                return AP_THREAT_YELLOW[1], AP_THREAT_YELLOW[2], AP_THREAT_YELLOW[3]
            end
        end
        return AP_THREAT_GREEN[1], AP_THREAT_GREEN[2], AP_THREAT_GREEN[3]
    end
end

-- ============================================================
-- Detect nameplate
-- ============================================================
local function IsNamePlate(frame)
    if not AP_HAS_SUPERWOW then return false end
    local guid = frame:GetName(1)
    return frame:IsObjectType("Button")
        and (guid and guid ~= "0x0000000000000000")
        and (frame:GetChildren() and frame:GetChildren():IsObjectType("StatusBar"))
end

-- ============================================================
-- Hook helper (like TankPlates)
-- ============================================================
local function HookScript(f, script, func)
    local prev = f:GetScript(script)
    f:SetScript(script, function(a1,a2,a3,a4,a5,a6,a7,a8,a9)
        if prev then prev(a1,a2,a3,a4,a5,a6,a7,a8,a9) end
        func(a1,a2,a3,a4,a5,a6,a7,a8,a9)
    end)
end

-- ============================================================
-- Initialize a nameplate (once per plate frame)
-- ============================================================
local function InitPlate(plate)
    local healthbar, castbar = plate:GetChildren()
    if not healthbar then return end

    local db = GetDB()
    local regions = { plate:GetRegions() }
    -- Vanilla: 1=border, 2=glow, 3=name, 4=level, 5=levelicon, 6=raidicon

    -- Store original healthbar color for unit type detection
    local origR, origG, origB = healthbar:GetStatusBarColor()

    -- Disable mouse on plate (prevents highlight)
    -- Right-click camera: forward right-click to mouselook
    if db.clickThrough then
        plate:SetScript("OnMouseDown", function()
            if arg1 == "RightButton" then
                MouselookStart()
            end
        end)
    end

    -- Lock alpha to 1 on plate AND healthbar (prevent Blizzard from fading)
    local origPlateSetAlpha = plate.SetAlpha
    plate.SetAlpha = function(s, a)
        origPlateSetAlpha(s, 1)
    end
    plate:SetAlpha(1)

    local origHBSetAlpha = healthbar.SetAlpha
    healthbar.SetAlpha = function(s, a)
        origHBSetAlpha(s, 1)
    end
    healthbar:SetAlpha(1)

    -- Strip Blizzard textures (pfUI style)
    for i = 1, 5 do
        local obj = regions[i]
        if obj then
            local otype = obj:GetObjectType()
            if otype == "Texture" then
                obj:SetTexture("")
                obj:SetTexCoord(0, 0, 0, 0)
            elseif otype == "FontString" then
                obj:SetWidth(0.001)
            end
        end
    end

    -- Restyle healthbar: flat texture + correct size immediately
    healthbar:SetStatusBarTexture("Interface\\Buttons\\WHITE8X8")
    healthbar:ClearAllPoints()
    healthbar:SetPoint("TOP", plate, "TOP", 0, 0)
    healthbar:SetWidth(db.barWidth)
    healthbar:SetHeight(db.barHeight)

    -- Use Region 1 (Blizzard nameplate border) as our background
    -- Instead of stripping it, repurpose it as a dark fill behind the healthbar
    -- Background bar: a second StatusBar at 100% behind the real healthbar
    local hpBgBar = CreateFrame("StatusBar", nil, plate)
    hpBgBar:SetStatusBarTexture("Interface\\Buttons\\WHITE8X8")
    hpBgBar:SetStatusBarColor(0, 0, 0, 0.7)
    hpBgBar:SetMinMaxValues(0, 1)
    hpBgBar:SetValue(1)
    hpBgBar:SetAllPoints(healthbar)
    hpBgBar:SetFrameLevel(healthbar:GetFrameLevel())
    -- Push healthbar above background bar
    healthbar:SetFrameLevel(hpBgBar:GetFrameLevel() + 1)

    -- Border frame around healthbar
    local hpBg = CreateFrame("Frame", nil, healthbar)
    hpBg:SetPoint("TOPLEFT", healthbar, "TOPLEFT", -2, 2)
    hpBg:SetPoint("BOTTOMRIGHT", healthbar, "BOTTOMRIGHT", 2, -2)
    hpBg:SetFrameLevel(healthbar:GetFrameLevel() + 1)
    hpBg:SetBackdrop(AP_BACKDROP)
    hpBg:SetBackdropColor(0, 0, 0, 0)
    hpBg:SetBackdropBorderColor(0.30, 0.30, 0.30, 1)

    -- Name text (above healthbar)
    local nameFS = healthbar:CreateFontString(nil, "OVERLAY")
    nameFS:SetFont("Fonts\\FRIZQT__.TTF", 9, "OUTLINE")
    nameFS:SetPoint("BOTTOM", healthbar, "TOP", 0, 3)
    nameFS:SetTextColor(1, 1, 1, 1)

    -- Level text (left of healthbar)
    local levelFS = healthbar:CreateFontString(nil, "OVERLAY")
    levelFS:SetFont("Fonts\\FRIZQT__.TTF", 8, "OUTLINE")
    levelFS:SetPoint("RIGHT", healthbar, "LEFT", -3, 0)
    levelFS:SetTextColor(1, 0.82, 0, 1)

    -- Boss skull icon (left of healthbar)
    local bossIcon = healthbar:CreateTexture(nil, "OVERLAY")
    bossIcon:SetTexture("Interface\\TargetingFrame\\UI-TargetingFrame-Skull")
    bossIcon:SetWidth(14)
    bossIcon:SetHeight(14)
    bossIcon:SetPoint("RIGHT", healthbar, "LEFT", -1, 0)
    bossIcon:Hide()

    -- HP percentage text (on healthbar)
    local hpText = healthbar:CreateFontString(nil, "OVERLAY")
    hpText:SetFont("Fonts\\FRIZQT__.TTF", 7, "OUTLINE")
    hpText:SetPoint("CENTER", healthbar, "CENTER", 0, 0)
    hpText:SetTextColor(1, 1, 1, 0.9)

    -- Cast bar (new StatusBar below healthbar)
    local cbH = db.cbHeight

    local cb = CreateFrame("StatusBar", nil, healthbar)
    cb:SetStatusBarTexture("Interface\\Buttons\\WHITE8X8")
    cb:SetStatusBarColor(1.0, 0.7, 0.0, 1)
    cb:SetMinMaxValues(0, 1)
    cb:SetValue(0)
    cb:SetPoint("TOPLEFT", healthbar, "BOTTOMLEFT", 0, -3)
    cb:SetPoint("TOPRIGHT", healthbar, "BOTTOMRIGHT", 0, -3)
    cb:SetHeight(cbH)
    cb:Hide()

    local cbBg = CreateFrame("Frame", nil, cb)
    cbBg:SetPoint("TOPLEFT", cb, "TOPLEFT", -1, 1)
    cbBg:SetPoint("BOTTOMRIGHT", cb, "BOTTOMRIGHT", 1, -1)
    cbBg:SetFrameLevel(cb:GetFrameLevel() - 1)
    cbBg:SetBackdrop(AP_BACKDROP)
    cbBg:SetBackdropColor(0.05, 0.05, 0.05, 0.85)
    cbBg:SetBackdropBorderColor(0.10, 0.10, 0.10, 1)

    -- Cast bar spell icon
    local cbIcon = CreateFrame("Frame", nil, healthbar)
    cbIcon:SetWidth(cbH)
    cbIcon:SetHeight(cbH)
    cbIcon:SetPoint("TOPRIGHT", healthbar, "BOTTOMLEFT", -3, -3)
    cbIcon:Hide()

    local cbIconTex = cbIcon:CreateTexture(nil, "ARTWORK")
    cbIconTex:SetAllPoints(cbIcon)
    cbIconTex:SetTexCoord(0.1, 0.9, 0.1, 0.9)

    local cbIconBg = CreateFrame("Frame", nil, cbIcon)
    cbIconBg:SetPoint("TOPLEFT", cbIcon, "TOPLEFT", -1, 1)
    cbIconBg:SetPoint("BOTTOMRIGHT", cbIcon, "BOTTOMRIGHT", 1, -1)
    cbIconBg:SetFrameLevel(cbIcon:GetFrameLevel() - 1)
    cbIconBg:SetBackdrop(AP_BACKDROP)
    cbIconBg:SetBackdropColor(0.05, 0.05, 0.05, 0.85)
    cbIconBg:SetBackdropBorderColor(0.10, 0.10, 0.10, 1)

    -- Aura icons (right of healthbar)
    local auraIcons = {}
    for ai = 1, AP_MAX_AURA_ICONS do
        local aIcon = CreateFrame("Frame", nil, healthbar)
        local iconSize = db.barHeight
        aIcon:SetWidth(iconSize)
        aIcon:SetHeight(iconSize)
        if ai == 1 then
            aIcon:SetPoint("LEFT", healthbar, "RIGHT", 3, 0)
        else
            aIcon:SetPoint("LEFT", auraIcons[ai - 1], "RIGHT", 1, 0)
        end
        local aTex = aIcon:CreateTexture(nil, "ARTWORK")
        aTex:SetAllPoints(aIcon)
        aTex:SetTexCoord(0.1, 0.9, 0.1, 0.9)
        aIcon.tex = aTex
        local aCount = aIcon:CreateFontString(nil, "OVERLAY")
        aCount:SetFont("Fonts\\FRIZQT__.TTF", 7, "OUTLINE")
        aCount:SetPoint("BOTTOMRIGHT", aIcon, "BOTTOMRIGHT", 1, -1)
        aCount:SetTextColor(1, 1, 1, 1)
        aCount:Hide()
        aIcon.count = aCount
        aIcon:Hide()
        auraIcons[ai] = aIcon
    end

    -- Hide original castbar
    if castbar then
        castbar:SetStatusBarTexture("")
        castbar:SetAlpha(0)
        local cbRegs = { castbar:GetRegions() }
        for i = 1, getn(cbRegs) do
            local obj = cbRegs[i]
            if obj then
                local otype = obj:GetObjectType()
                if otype == "Texture" then
                    obj:SetTexture("")
                    obj:SetTexCoord(0, 0, 0, 0)
                elseif otype == "FontString" then
                    obj:SetWidth(0.001)
                end
            end
        end
    end

    -- Store data on plate
    local pd = {
        healthbar = healthbar,
        castbar   = castbar,
        regions   = regions,
        hpBg      = hpBg,
        nameFS    = nameFS,
        levelFS   = levelFS,
        bossIcon  = bossIcon,
        hpText    = hpText,
        cb        = cb,
        cbIcon    = cbIcon,
        cbIconTex = cbIconTex,
        origColor = { origR, origG, origB },
        curColor  = { 0.90, 0.20, 0.30 },
        auraIcons = auraIcons,
    }
    registry[plate] = pd

    -- Lightweight per-frame hook: only reapply texture + cached color (no logic)
    local function ReapplyColor()
        local p = this:GetParent()
        local d = registry[p]
        if not d then return end
        this:SetStatusBarTexture("Interface\\Buttons\\WHITE8X8")
        this:SetStatusBarColor(d.curColor[1], d.curColor[2], d.curColor[3], 1)
    end

    -- HP percentage update (only on value change, not every frame)
    local function UpdateHPText()
        local p = this:GetParent()
        local d = registry[p]
        if not d then return end
        local mn, mx = this:GetMinMaxValues()
        local val = this:GetValue()
        local pct = 100
        if mx > 0 then pct = floor(val / mx * 100) end
        d.hpText:SetText(pct .. "%")
    end

    HookScript(healthbar, "OnUpdate", ReapplyColor)
    HookScript(healthbar, "OnValueChanged", ReapplyColor)
    HookScript(healthbar, "OnValueChanged", UpdateHPText)

    -- Hook plate OnShow for recycled plates
    HookScript(plate, "OnShow", function()
        local d = registry[this]
        if not d then return end

        -- Recapture original color for unit type
        local r, g, b = d.healthbar:GetStatusBarColor()
        -- Only store if it looks like a valid Blizzard color (not our override)
        if (r > 0.5 and g < 0.5) or (r > 0.5 and g > 0.5 and b < 0.5) then
            d.origColor[1], d.origColor[2], d.origColor[3] = r, g, b
        end

        -- Reset caches for recycled plate (new mob)
        d.levelCached = false

        -- Re-strip Blizzard textures
        for i = 1, 5 do
            local obj = d.regions[i]
            if obj then
                local otype = obj:GetObjectType()
                if otype == "Texture" then
                    obj:SetTexture("")
                    obj:SetTexCoord(0, 0, 0, 0)
                elseif otype == "FontString" then
                    obj:SetWidth(0.001)
                end
            end
        end
        d.healthbar:SetStatusBarTexture("Interface\\Buttons\\WHITE8X8")
        local ddb = GetDB()
        d.healthbar:ClearAllPoints()
        d.healthbar:SetPoint("TOP", this, "TOP", 0, 0)
        d.healthbar:SetWidth(ddb.barWidth)
        d.healthbar:SetHeight(ddb.barHeight)
    end)
end

-- ============================================================
-- Throttled scan: update name, level, target highlight, layout
-- ============================================================
local function UpdatePlate(plate)
    local pd = registry[plate]
    if not pd then return end

    local db = GetDB()
    local healthbar = pd.healthbar
    local regions = pd.regions

    -- Resize healthbar
    healthbar:ClearAllPoints()
    healthbar:SetPoint("TOP", plate, "TOP", 0, 0)
    healthbar:SetWidth(db.barWidth)
    healthbar:SetHeight(db.barHeight)

    -- Threat color calculation (runs every 0.1s, not every frame)
    local unitType = GetUnitType(pd.origColor[1], pd.origColor[2], pd.origColor[3])
    if unitType then
        local guid = AP_GetGuid(plate)

        -- Enemy players: always class color (no threat on players)
        local isPlayer = guid and AP_HAS_SUPERWOW and UnitIsPlayer(guid)
        if isPlayer then
            local _, classToken = UnitClass(guid)
            local classCol = classToken and AP_CLASS_COLORS[classToken]
            if classCol then
                pd.curColor[1], pd.curColor[2], pd.curColor[3] = classCol[1], classCol[2], classCol[3]
                pd.hpBg:SetBackdropBorderColor(classCol[1] * 0.6, classCol[2] * 0.6, classCol[3] * 0.6, 1)
            end
        else
            -- NPCs: threat color or default
            local tr, tg, tb = GetThreatColor(plate, guid, db)
            if tr then
                pd.curColor[1], pd.curColor[2], pd.curColor[3] = tr, tg, tb
                pd.hpBg:SetBackdropBorderColor(tr * 0.6, tg * 0.6, tb * 0.6, 1)
            else
                local col = AP_COLORS[unitType] or AP_COLORS.ENEMY_NPC
                pd.curColor[1], pd.curColor[2], pd.curColor[3] = col[1], col[2], col[3]
                pd.hpBg:SetBackdropBorderColor(0.30, 0.30, 0.30, 1)
            end
        end
    end

    -- Name
    if regions[3] then
        local nameText = regions[3]:GetText()
        if nameText then pd.nameFS:SetText(nameText) end
    end

    -- Level + classification (skip if cached in high tiers)
    if activeTier.levelCache and pd.levelCached then
        -- Use cached level text, skip recalculation
    elseif regions[4] then
        local lvlText = regions[4]:GetText()
        if lvlText then
            pd.levelCached = true
            local isBoss = (lvlText == "??")
            local classification = nil
            if AP_HAS_SUPERWOW then
                local guid = AP_GetGuid(plate)
                if guid then classification = UnitClassification(guid) end
            end

            if isBoss or classification == "worldboss" then
                pd.levelFS:SetText("")
                pd.levelFS:Hide()
                pd.bossIcon:Show()
            else
                pd.bossIcon:Hide()
                pd.levelFS:Show()
                local prefix = ""
                if classification == "elite" then
                    prefix = "E"
                elseif classification == "rareelite" then
                    prefix = "R+"
                elseif classification == "rare" then
                    prefix = "R"
                end
                local lr, lg, lb = regions[4]:GetTextColor()
                if prefix ~= "" then
                    local prefixColor
                    if classification == "rare" or classification == "rareelite" then
                        prefixColor = "|cFFC4C4C4"
                    else
                        prefixColor = "|cFFFFD100"
                    end
                    local r2 = floor((lr + 0.2) * 255)
                    local g2 = floor((lg + 0.2) * 255)
                    local b2 = floor((lb + 0.2) * 255)
                    if r2 > 255 then r2 = 255 end
                    if g2 > 255 then g2 = 255 end
                    if b2 > 255 then b2 = 255 end
                    local lvlColor = string.format("|cFF%02X%02X%02X", r2, g2, b2)
                    pd.levelFS:SetText(prefixColor .. prefix .. lvlColor .. lvlText .. "|r")
                else
                    pd.levelFS:SetText(lvlText)
                end
                pd.levelFS:SetTextColor(lr + 0.2, lg + 0.2, lb + 0.2, 1)
            end
        end
    end

    -- Raid icon
    if regions[6] and regions[6]:IsShown() then
        regions[6]:ClearAllPoints()
        regions[6]:SetPoint("BOTTOM", pd.nameFS, "TOP", 0, 2)
        regions[6]:SetWidth(14)
        regions[6]:SetHeight(14)
    end

    -- Target highlight
    if AP_HAS_SUPERWOW then
        local guid = AP_GetGuid(plate)
        if guid and UnitIsUnit("target", guid) then
            pd.nameFS:SetTextColor(1, 1, 0, 1)
        else
            pd.nameFS:SetTextColor(1, 1, 1, 1)
        end
    end

    -- Castbar layout
    local cbH = db.cbHeight
    pd.cb:SetHeight(cbH)
    pd.cbIcon:SetWidth(cbH)
    pd.cbIcon:SetHeight(cbH)

    -- Aura icons layout + scan
    for ai = 1, AP_MAX_AURA_ICONS do
        pd.auraIcons[ai]:SetWidth(db.barHeight)
        pd.auraIcons[ai]:SetHeight(db.barHeight)
    end
    if AP_CAN_TRACK_AURAS then
        local guid = AP_GetGuid(plate)
        AP_ScanAuras(plate, pd, guid)
    end
end

-- ============================================================
-- Castbar update (throttled by tier)
-- ============================================================
local cbTimer = 0
local function UpdateCastbars(dt)
    local throttle = activeTier.cbThrottle
    if throttle > 0 then
        cbTimer = cbTimer + dt
        if cbTimer < throttle then return end
        cbTimer = 0
    end

    local libcasts = pfUI and pfUI.libdebuff_casts
    for plate, pd in pairs(registry) do
        if plate:IsShown() then
            local origCast = pd.castbar
            if origCast and origCast:IsShown() then
                local cbMin, cbMax = origCast:GetMinMaxValues()
                local cbVal = origCast:GetValue()
                pd.cb:SetMinMaxValues(cbMin, cbMax)
                pd.cb:SetValue(cbVal)
                if not pd.cb:IsShown() then pd.cb:Show() end

                if AP_HAS_SUPERWOW and libcasts then
                    local guid = AP_GetGuid(plate)
                    if guid then
                        local castInfo = libcasts[guid]
                        if castInfo and castInfo.icon then
                            pd.cbIconTex:SetTexture(castInfo.icon)
                            if not pd.cbIcon:IsShown() then pd.cbIcon:Show() end
                        end
                    end
                end
            else
                if pd.cb:IsShown() then
                    pd.cb:Hide()
                    pd.cbIcon:Hide()
                end
            end
        end
    end
end

-- ============================================================
-- Main scan loop (with tier-based throttling + staggering)
-- ============================================================
local scanTimer = 0
local staggerIndex = 0

local mainFrame = CreateFrame("Frame", "AmptiePlatesMain", UIParent)
mainFrame:RegisterEvent("PLAYER_ENTERING_WORLD")
mainFrame:RegisterEvent("PLAYER_TARGET_CHANGED")
if AP_HAS_SUPERWOW then
    mainFrame:RegisterEvent("UNIT_CASTEVENT")
end
mainFrame:RegisterEvent("CHAT_MSG_ADDON")

mainFrame:SetScript("OnUpdate", function()
    local db = GetDB()
    if not db.enabled then return end

    local dt = arg1 or 0
    UpdateCastbars(dt)

    -- Overlap: force plate size to 1x1 every frame (client constantly resets it)
    if db.overlap then
        for plate in pairs(registry) do
            if plate:GetWidth() > 1 then
                plate:SetWidth(1)
                plate:SetHeight(1)
            end
        end
    end

    -- Threat sharing timer (tier-dependent interval + jitter)
    shareTimer = shareTimer + dt
    if shareTimer >= activeTier.share + shareJitter then
        shareTimer = 0
        AP_ShareThreat()
    end

    -- Stale cleanup for shared threats
    local now = GetTime()
    for guid, sdata in pairs(AP_SharedThreats) do
        if sdata._time and (now - sdata._time) > AP_SHARE_STALE then
            AP_SharedThreats[guid] = nil
        end
    end

    scanTimer = scanTimer + dt
    if scanTimer < activeTier.scan then return end
    scanTimer = 0

    -- Count in-combat plates and update tier
    local inCombat = 0
    local plates = {}
    local plateCount = 0

    local children = { WorldFrame:GetChildren() }
    for i = 1, getn(children) do
        local plate = children[i]
        if plate:IsShown() then
            if not registry[plate] then
                if IsNamePlate(plate) then
                    InitPlate(plate)
                end
            end
            if registry[plate] then
                plateCount = plateCount + 1
                plates[plateCount] = plate
                local guid = AP_GetGuid(plate)
                if guid and UnitAffectingCombat(guid) then
                    inCombat = inCombat + 1
                end
            end
        end
    end

    combatPlateCount = inCombat
    activeTier = GetTier(inCombat)

    -- Staggered updates: only update N plates per scan cycle
    local stagger = activeTier.stagger
    if stagger > 0 and plateCount > stagger then
        local updated = 0
        for s = 1, plateCount do
            staggerIndex = staggerIndex + 1
            if staggerIndex > plateCount then staggerIndex = 1 end
            UpdatePlate(plates[staggerIndex])
            updated = updated + 1
            if updated >= stagger then break end
        end
    else
        for i = 1, plateCount do
            UpdatePlate(plates[i])
        end
    end
end)

mainFrame:SetScript("OnEvent", function()
    local evt = event
    local a1, a2, a3 = arg1, arg2, arg3
    if evt == "PLAYER_ENTERING_WORLD" then
        if AP_HAS_SUPERWOW then
            local _, guid = UnitExists("player")
            playerGuid = guid
        end
    elseif evt == "PLAYER_TARGET_CHANGED" then
        for plate, pd in pairs(registry) do
            if plate:IsShown() then UpdatePlate(plate) end
        end
    elseif evt == "UNIT_CASTEVENT" then
        local _, sourceGuid = UnitExists(a1)
        local _, castTarget = UnitExists(a2)
        if sourceGuid then
            local unit = tracked[sourceGuid]
            if unit then
                if a3 == "START" then
                    unit.casting = true
                    unit.casting_at = castTarget
                elseif a3 == "FAIL" or a3 == "CAST" then
                    unit.casting = false
                    unit.casting_at = nil
                    if unit.previous_target then
                        unit.current_target = unit.previous_target
                    end
                end
            end
        end
    elseif evt == "CHAT_MSG_ADDON" then
        -- a1 = prefix, a2 = message, a3 = channel, arg4 = sender
        if a1 == AP_SHARE_PREFIX then
            AP_ReceiveThreat(a2)
        end
    end
end)

-- ============================================================
-- Settings panel
-- ============================================================
local settingsFrame = nil
local settingsUpdateMode = nil  -- set by CreateSettingsFrame

local function AP_MakeSlider(parent, label, min, max, step, val, x, y, onChange)
    local lbl = parent:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    lbl:SetPoint("TOPLEFT", parent, "TOPLEFT", x, y)
    lbl:SetTextColor(0.8, 0.8, 0.85, 1)
    lbl:SetText(label .. ": " .. val)

    local sl = CreateFrame("Slider", nil, parent)
    sl:SetWidth(130); sl:SetHeight(14)
    sl:SetPoint("LEFT", lbl, "RIGHT", 10, 0)
    sl:SetOrientation("HORIZONTAL")
    sl:SetMinMaxValues(min, max); sl:SetValueStep(step); sl:SetValue(val)
    local th = sl:CreateTexture(nil, "OVERLAY")
    th:SetWidth(10); th:SetHeight(14); th:SetTexture(0.5, 0.5, 0.55, 0.9)
    sl:SetThumbTexture(th)
    local tr = sl:CreateTexture(nil, "BACKGROUND")
    tr:SetAllPoints(sl); tr:SetTexture(0.12, 0.12, 0.15, 0.8)
    sl:SetScript("OnValueChanged", function()
        local v = floor(this:GetValue())
        lbl:SetText(label .. ": " .. v)
        if onChange then onChange(v) end
    end)
    return lbl, sl
end

local function CreateSettingsFrame()
    local BD = {
        bgFile   = "Interface\\Tooltips\\UI-Tooltip-Background",
        edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
        tile = true, tileSize = 16, edgeSize = 12,
        insets = { left=3, right=3, top=3, bottom=3 },
    }
    local f = CreateFrame("Frame", "AmptiePlatesSettings", UIParent)
    f:SetWidth(320); f:SetHeight(230)
    f:SetPoint("CENTER", UIParent, "CENTER", 0, 100)
    f:SetFrameStrata("DIALOG")
    f:SetMovable(true); f:SetClampedToScreen(true)
    f:RegisterForDrag("LeftButton"); f:EnableMouse(true)
    f:SetScript("OnDragStart", function() this:StartMoving() end)
    f:SetScript("OnDragStop", function() this:StopMovingOrSizing() end)
    f:SetBackdrop(BD)
    f:SetBackdropColor(0.06, 0.06, 0.08, 0.95)
    f:SetBackdropBorderColor(0.35, 0.35, 0.4, 1)
    f:Hide()
    tinsert(UISpecialFrames, "AmptiePlatesSettings")

    local title = f:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    title:SetPoint("TOPLEFT", f, "TOPLEFT", 12, -12)
    title:SetText("amptiePlates")
    title:SetTextColor(1, 0.82, 0, 1)

    local closeBtn = CreateFrame("Button", nil, f, "UIPanelCloseButton")
    closeBtn:SetWidth(22); closeBtn:SetHeight(22)
    closeBtn:SetPoint("TOPRIGHT", f, "TOPRIGHT", -2, -2)
    closeBtn:SetScript("OnClick", function() f:Hide() end)

    local db = GetDB()

    -- Enable checkbox
    local cbEnabled = CreateFrame("Button", nil, f)
    cbEnabled:SetWidth(16); cbEnabled:SetHeight(16)
    cbEnabled:SetPoint("TOPLEFT", f, "TOPLEFT", 14, -42)
    cbEnabled:SetBackdrop({ bgFile="Interface\\Buttons\\WHITE8X8", edgeFile="Interface\\Buttons\\WHITE8X8", edgeSize=1, insets={left=0,right=0,top=0,bottom=0} })
    local cbChk = cbEnabled:CreateTexture(nil, "OVERLAY")
    cbChk:SetTexture("Interface\\Buttons\\UI-CheckBox-Check")
    cbChk:SetAllPoints(cbEnabled)
    if db.enabled then cbChk:Show() else cbChk:Hide() end
    cbEnabled:SetScript("OnClick", function()
        local d = GetDB()
        d.enabled = not d.enabled
        if d.enabled then cbChk:Show() else cbChk:Hide() end
    end)
    local cbLbl = f:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    cbLbl:SetPoint("LEFT", cbEnabled, "RIGHT", 6, 0)
    cbLbl:SetText("Enable Nameplates")

    -- Click-through checkbox
    local cbClick = CreateFrame("Button", nil, f)
    cbClick:SetWidth(16); cbClick:SetHeight(16)
    cbClick:SetPoint("TOPLEFT", f, "TOPLEFT", 160, -42)
    cbClick:SetBackdrop({ bgFile="Interface\\Buttons\\WHITE8X8", edgeFile="Interface\\Buttons\\WHITE8X8", edgeSize=1, insets={left=0,right=0,top=0,bottom=0} })
    local cbClickChk = cbClick:CreateTexture(nil, "OVERLAY")
    cbClickChk:SetTexture("Interface\\Buttons\\UI-CheckBox-Check")
    cbClickChk:SetAllPoints(cbClick)
    if db.clickThrough then cbClickChk:Show() else cbClickChk:Hide() end
    cbClick:SetScript("OnClick", function()
        local d = GetDB()
        d.clickThrough = not d.clickThrough
        if d.clickThrough then cbClickChk:Show() else cbClickChk:Hide() end
        -- Apply immediately to all existing plates
        for plate, pd in pairs(registry) do
            if d.clickThrough then
                plate:SetScript("OnMouseDown", function()
                    if arg1 == "RightButton" then
                        MouselookStart()
                    end
                end)
            else
                plate:SetScript("OnMouseDown", nil)
            end
        end
    end)
    local cbClickLbl = f:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    cbClickLbl:SetPoint("LEFT", cbClick, "RIGHT", 6, 0)
    cbClickLbl:SetText("RMB Camera")

    -- Overlap checkbox (second row)
    local cbOverlap = CreateFrame("Button", nil, f)
    cbOverlap:SetWidth(16); cbOverlap:SetHeight(16)
    cbOverlap:SetPoint("TOPLEFT", f, "TOPLEFT", 14, -58)
    cbOverlap:SetBackdrop({ bgFile="Interface\\Buttons\\WHITE8X8", edgeFile="Interface\\Buttons\\WHITE8X8", edgeSize=1, insets={left=0,right=0,top=0,bottom=0} })
    local cbOverlapChk = cbOverlap:CreateTexture(nil, "OVERLAY")
    cbOverlapChk:SetTexture("Interface\\Buttons\\UI-CheckBox-Check")
    cbOverlapChk:SetAllPoints(cbOverlap)
    if db.overlap then cbOverlapChk:Show() else cbOverlapChk:Hide() end
    cbOverlap:SetScript("OnClick", function()
        local d = GetDB()
        d.overlap = not d.overlap
        if d.overlap then cbOverlapChk:Show() else cbOverlapChk:Hide() end
        -- Apply immediately
        for plate, pd in pairs(registry) do
            if d.overlap then
                plate:SetWidth(1)
                plate:SetHeight(1)
            else
                plate:SetWidth(db.barWidth + 40)
                plate:SetHeight(db.barHeight + 40)
            end
        end
    end)
    local cbOverlapLbl = f:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    cbOverlapLbl:SetPoint("LEFT", cbOverlap, "RIGHT", 6, 0)
    cbOverlapLbl:SetText("Allow Overlap")

    AP_MakeSlider(f, "Bar Width", 60, 200, 5, db.barWidth, 14, -80, function(v)
        GetDB().barWidth = v
    end)

    AP_MakeSlider(f, "Bar Height", 4, 24, 1, db.barHeight, 14, -104, function(v)
        GetDB().barHeight = v
    end)

    AP_MakeSlider(f, "Cast Height", 3, 16, 1, db.cbHeight, 14, -128, function(v)
        GetDB().cbHeight = v
    end)

    -- Mode toggle
    local modeLbl = f:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    modeLbl:SetPoint("TOPLEFT", f, "TOPLEFT", 14, -156)
    modeLbl:SetText("Mode:")
    modeLbl:SetTextColor(0.8, 0.8, 0.85, 1)

    local modeBtn = CreateFrame("Button", nil, f)
    modeBtn:SetWidth(100); modeBtn:SetHeight(22)
    modeBtn:SetPoint("LEFT", modeLbl, "RIGHT", 10, 0)
    modeBtn:SetBackdrop(BD)
    modeBtn:SetBackdropColor(0.12, 0.12, 0.15, 0.95)
    modeBtn:SetBackdropBorderColor(0.35, 0.35, 0.4, 1)
    modeBtn:SetHighlightTexture("Interface\\Buttons\\UI-Common-MouseHilight", "ADD")
    local modeFS = modeBtn:CreateFontString(nil, "OVERLAY", "GameFontHighlight")
    modeFS:SetAllPoints(modeBtn); modeFS:SetJustifyH("CENTER")

    local function UpdateModeBtn()
        local d = GetDB()
        if d.mode == "tank" then
            modeFS:SetText("|cFF55DD55Tank|r")
            modeBtn:SetBackdropBorderColor(0.3, 0.9, 0.3, 1)
        else
            modeFS:SetText("|cFFFF6644DPS / Heal|r")
            modeBtn:SetBackdropBorderColor(0.9, 0.3, 0.3, 1)
        end
    end
    settingsUpdateMode = UpdateModeBtn
    UpdateModeBtn()

    modeBtn:SetScript("OnClick", function()
        local d = GetDB()
        d.mode = (d.mode == "tank") and "dps" or "tank"
        UpdateModeBtn()
        local modeStr = d.mode == "tank" and "|cFF55DD55Tank|r" or "|cFFFF6644DPS/Healer|r"
        DEFAULT_CHAT_FRAME:AddMessage("|cffffff00[amptiePlates]|r Mode: " .. modeStr)
    end)

    -- Spell icon lookup helper
    local function AP_GetSpellIcon(spellName)
        if not spellName or spellName == "" then return "Interface\\Icons\\INV_Misc_QuestionMark" end
        -- Nampower DBC lookup (works for all spells)
        if _G.GetSpellIdForName and _G.GetSpellRecField and _G.GetSpellIconTexture then
            local spellId = GetSpellIdForName(spellName)
            if spellId then
                local iconId = GetSpellRecField(spellId, "spellIconID")
                if iconId and type(iconId) == "number" and iconId > 0 then
                    local tex = GetSpellIconTexture(iconId)
                    if tex then
                        if not sfind(tex, "\\") then tex = "Interface\\Icons\\" .. tex end
                        return tex
                    end
                end
            end
        end
        -- Fallback: scan player spellbook
        for tab = 1, GetNumSpellTabs() do
            local _, _, offset, numSpells = GetSpellTabInfo(tab)
            for si = offset + 1, offset + numSpells do
                local name = GetSpellName(si, BOOKTYPE_SPELL)
                if not name then break end
                if name == spellName then
                    return GetSpellTexture(si, BOOKTYPE_SPELL)
                end
            end
        end
        return "Interface\\Icons\\INV_Misc_QuestionMark"
    end

    -- Whitelist popup creator
    local function CreateWhitelistPopup(title, whitelistKey, anchorBtn)
        local popName = "AmptiePlatesWL_" .. whitelistKey
        -- Reuse existing popup if already created
        if _G[popName] then
            _G[popName].Refresh()
            _G[popName]:Show()
            return
        end

        local pop = CreateFrame("Frame", popName, UIParent)
        pop:SetWidth(260); pop:SetHeight(340)
        pop:SetFrameStrata("FULLSCREEN_DIALOG")
        pop:SetMovable(true); pop:SetClampedToScreen(true)
        pop:RegisterForDrag("LeftButton"); pop:EnableMouse(true)
        pop:SetScript("OnDragStart", function() this:StartMoving() end)
        pop:SetScript("OnDragStop", function() this:StopMovingOrSizing() end)
        pop:SetBackdrop({
            bgFile   = "Interface\\Buttons\\WHITE8X8",
            edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
            tile = true, tileSize = 16, edgeSize = 12,
            insets = { left=3, right=3, top=3, bottom=3 },
        })
        pop:SetBackdropColor(0.06, 0.06, 0.08, 1)
        pop:SetBackdropBorderColor(0.35, 0.35, 0.4, 1)
        pop:SetPoint("LEFT", anchorBtn, "RIGHT", 8, 0)
        tinsert(UISpecialFrames, popName)

        local popTitle = pop:CreateFontString(nil, "OVERLAY", "GameFontNormal")
        popTitle:SetPoint("TOPLEFT", pop, "TOPLEFT", 10, -10)
        popTitle:SetText(title)
        popTitle:SetTextColor(1, 0.82, 0, 1)

        local popClose = CreateFrame("Button", nil, pop, "UIPanelCloseButton")
        popClose:SetWidth(20); popClose:SetHeight(20)
        popClose:SetPoint("TOPRIGHT", pop, "TOPRIGHT", -2, -2)
        popClose:SetScript("OnClick", function() pop:Hide() end)

        -- Scroll area for entries
        local listArea = CreateFrame("Frame", nil, pop)
        listArea:SetPoint("TOPLEFT", pop, "TOPLEFT", 10, -30)
        listArea:SetPoint("BOTTOMRIGHT", pop, "BOTTOMRIGHT", -10, 40)

        local rows = {}
        local MAX_VISIBLE = 10

        -- Create row frames
        for ri = 1, MAX_VISIBLE do
            local row = CreateFrame("Frame", nil, listArea)
            row:SetWidth(236); row:SetHeight(20)
            if ri == 1 then
                row:SetPoint("TOPLEFT", listArea, "TOPLEFT", 0, 0)
            else
                row:SetPoint("TOPLEFT", rows[ri - 1], "BOTTOMLEFT", 0, -1)
            end

            local ico = row:CreateTexture(nil, "ARTWORK")
            ico:SetWidth(18); ico:SetHeight(18)
            ico:SetPoint("LEFT", row, "LEFT", 0, 0)
            ico:SetTexCoord(0.1, 0.9, 0.1, 0.9)
            row.icon = ico

            local nameFS = row:CreateFontString(nil, "OVERLAY")
            nameFS:SetFont("Fonts\\FRIZQT__.TTF", 9, "")
            nameFS:SetPoint("LEFT", ico, "RIGHT", 4, 0)
            nameFS:SetPoint("RIGHT", row, "RIGHT", -22, 0)
            nameFS:SetJustifyH("LEFT")
            nameFS:SetTextColor(1, 1, 1, 1)
            row.nameFS = nameFS

            local delBtn = CreateFrame("Button", nil, row)
            delBtn:SetWidth(16); delBtn:SetHeight(16)
            delBtn:SetPoint("RIGHT", row, "RIGHT", 0, 0)
            local delFS = delBtn:CreateFontString(nil, "OVERLAY")
            delFS:SetFont("Fonts\\FRIZQT__.TTF", 12, "OUTLINE")
            delFS:SetAllPoints(delBtn)
            delFS:SetText("|cFFFF4444x|r")
            delBtn:SetHighlightTexture("Interface\\Buttons\\UI-Common-MouseHilight", "ADD")
            delBtn.row = row
            delBtn:SetScript("OnClick", function()
                local spName = this.row.spellName
                if spName then
                    GetDB()[whitelistKey][spName] = nil
                    pop.Refresh()
                end
            end)
            row.delBtn = delBtn

            row:Hide()
            rows[ri] = row
        end

        -- Add section at bottom
        local addNameLbl = pop:CreateFontString(nil, "OVERLAY")
        addNameLbl:SetFont("Fonts\\FRIZQT__.TTF", 8, "OUTLINE")
        addNameLbl:SetPoint("BOTTOMLEFT", pop, "BOTTOMLEFT", 10, 58)
        addNameLbl:SetText("Spell Name:")
        addNameLbl:SetTextColor(0.6, 0.6, 0.65, 1)

        local addBox = CreateFrame("EditBox", nil, pop)
        addBox:SetFont("Fonts\\FRIZQT__.TTF", 9, "")
        addBox:SetWidth(236); addBox:SetHeight(18)
        addBox:SetPoint("TOPLEFT", addNameLbl, "BOTTOMLEFT", 0, -1)
        addBox:SetAutoFocus(false)
        addBox:SetBackdrop(BD)
        addBox:SetBackdropColor(0.1, 0.1, 0.12, 0.95)
        addBox:SetBackdropBorderColor(0.3, 0.3, 0.35, 1)
        addBox:SetTextInsets(4, 4, 2, 2)
        addBox:SetTextColor(1, 1, 1, 1)
        addBox:SetScript("OnEscapePressed", function() this:ClearFocus() end)

        local addTexLbl = pop:CreateFontString(nil, "OVERLAY")
        addTexLbl:SetFont("Fonts\\FRIZQT__.TTF", 8, "OUTLINE")
        addTexLbl:SetPoint("TOPLEFT", addBox, "BOTTOMLEFT", 0, -3)
        addTexLbl:SetText("Icon Path (optional):")
        addTexLbl:SetTextColor(0.6, 0.6, 0.65, 1)

        local addTexBox = CreateFrame("EditBox", nil, pop)
        addTexBox:SetFont("Fonts\\FRIZQT__.TTF", 8, "")
        addTexBox:SetWidth(200); addTexBox:SetHeight(16)
        addTexBox:SetPoint("TOPLEFT", addTexLbl, "BOTTOMLEFT", 0, -1)
        addTexBox:SetAutoFocus(false)
        addTexBox:SetBackdrop(BD)
        addTexBox:SetBackdropColor(0.1, 0.1, 0.12, 0.95)
        addTexBox:SetBackdropBorderColor(0.3, 0.3, 0.35, 1)
        addTexBox:SetTextInsets(4, 4, 2, 2)
        addTexBox:SetTextColor(0.7, 0.7, 0.7, 1)
        addTexBox:SetScript("OnEscapePressed", function() this:ClearFocus() end)

        local addBtn = CreateFrame("Button", nil, pop)
        addBtn:SetWidth(30); addBtn:SetHeight(16)
        addBtn:SetPoint("LEFT", addTexBox, "RIGHT", 2, 0)
        addBtn:SetBackdrop(BD)
        addBtn:SetBackdropColor(0.15, 0.4, 0.15, 0.95)
        addBtn:SetBackdropBorderColor(0.3, 0.6, 0.3, 1)
        addBtn:SetHighlightTexture("Interface\\Buttons\\UI-Common-MouseHilight", "ADD")
        local addFS = addBtn:CreateFontString(nil, "OVERLAY")
        addFS:SetFont("Fonts\\FRIZQT__.TTF", 9, "OUTLINE")
        addFS:SetAllPoints(addBtn); addFS:SetJustifyH("CENTER")
        addFS:SetText("+")
        addFS:SetTextColor(0.5, 1, 0.5, 1)

        local function DoAdd()
            local txt = addBox:GetText()
            local _, _, trimmed = sfind(txt, "^%s*(.-)%s*$")
            if trimmed and trimmed ~= "" then
                local texPath = addTexBox:GetText()
                local _, _, texTrimmed = sfind(texPath, "^%s*(.-)%s*$")
                if texTrimmed and texTrimmed ~= "" then
                    if not sfind(texTrimmed, "\\") then
                        texTrimmed = "Interface\\Icons\\" .. texTrimmed
                    end
                    GetDB()[whitelistKey][trimmed] = texTrimmed
                else
                    GetDB()[whitelistKey][trimmed] = true
                end
                addBox:SetText("")
                addTexBox:SetText("")
                pop.Refresh()
            end
            addBox:ClearFocus()
            addTexBox:ClearFocus()
        end

        addBtn:SetScript("OnClick", DoAdd)
        addBox:SetScript("OnEnterPressed", DoAdd)
        addTexBox:SetScript("OnEnterPressed", DoAdd)

        function pop.Refresh()
            local wl = GetDB()[whitelistKey]
            local idx = 0
            for spName, val in pairs(wl) do
                idx = idx + 1
                if idx > MAX_VISIBLE then break end
                local row = rows[idx]
                row.spellName = spName
                -- val is either true (auto-icon) or a string (manual texture path)
                if type(val) == "string" then
                    row.icon:SetTexture(val)
                else
                    row.icon:SetTexture(AP_GetSpellIcon(spName))
                end
                row.nameFS:SetText(spName)
                row:Show()
            end
            for i = idx + 1, MAX_VISIBLE do
                rows[i]:Hide()
            end
        end

        pop.Refresh()
        pop:Show()
    end

    -- Debuff Whitelist button
    local dwlBtn = CreateFrame("Button", nil, f)
    dwlBtn:SetWidth(140); dwlBtn:SetHeight(20)
    dwlBtn:SetPoint("TOPLEFT", f, "TOPLEFT", 14, -188)
    dwlBtn:SetBackdrop(BD)
    dwlBtn:SetBackdropColor(0.12, 0.12, 0.15, 0.95)
    dwlBtn:SetBackdropBorderColor(0.35, 0.35, 0.4, 1)
    dwlBtn:SetHighlightTexture("Interface\\Buttons\\UI-Common-MouseHilight", "ADD")
    local dwlFS = dwlBtn:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    dwlFS:SetAllPoints(dwlBtn); dwlFS:SetJustifyH("CENTER")
    dwlFS:SetText("Debuff Whitelist")
    if not AP_CAN_TRACK_AURAS then
        dwlFS:SetTextColor(0.5, 0.5, 0.5, 1)
        dwlBtn:Disable()
    end
    dwlBtn:SetScript("OnClick", function()
        CreateWhitelistPopup("Debuff Whitelist", "debuffWhitelist", this)
    end)

    -- Buff Whitelist button
    local bwlBtn = CreateFrame("Button", nil, f)
    bwlBtn:SetWidth(140); bwlBtn:SetHeight(20)
    bwlBtn:SetPoint("LEFT", dwlBtn, "RIGHT", 6, 0)
    bwlBtn:SetBackdrop(BD)
    bwlBtn:SetBackdropColor(0.12, 0.12, 0.15, 0.95)
    bwlBtn:SetBackdropBorderColor(0.35, 0.35, 0.4, 1)
    bwlBtn:SetHighlightTexture("Interface\\Buttons\\UI-Common-MouseHilight", "ADD")
    local bwlFS = bwlBtn:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
    bwlFS:SetAllPoints(bwlBtn); bwlFS:SetJustifyH("CENTER")
    bwlFS:SetText("Buff Whitelist")
    if not AP_CAN_TRACK_AURAS then
        bwlFS:SetTextColor(0.5, 0.5, 0.5, 1)
        bwlBtn:Disable()
    end
    bwlBtn:SetScript("OnClick", function()
        CreateWhitelistPopup("Buff Whitelist", "buffWhitelist", this)
    end)

    if not AP_CAN_TRACK_AURAS then
        local noAura = f:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
        noAura:SetPoint("TOPLEFT", dwlBtn, "BOTTOMLEFT", 0, -4)
        noAura:SetText("|cFF888888Requires pfUI or SuperWoW|r")
    end

    settingsFrame = f
end

-- ============================================================
-- Minimap button
-- ============================================================
local function CreateMinimapButton()
    local db = GetDB()
    local btn = CreateFrame("Button", "AmptiePlatesMinimapBtn", Minimap)
    btn:SetWidth(31); btn:SetHeight(31)
    btn:SetFrameStrata("MEDIUM")
    btn:SetFrameLevel(8)
    btn:SetHighlightTexture("Interface\\Minimap\\UI-Minimap-ZoomButton-Highlight")
    btn:RegisterForClicks("LeftButtonUp", "RightButtonUp")
    btn:RegisterForDrag("LeftButton")

    local overlay = btn:CreateTexture(nil, "OVERLAY")
    overlay:SetWidth(53); overlay:SetHeight(53)
    overlay:SetTexture("Interface\\Minimap\\MiniMap-TrackingBorder")
    overlay:SetPoint("TOPLEFT", btn, "TOPLEFT", 0, 0)

    local icon = btn:CreateTexture(nil, "BACKGROUND")
    icon:SetWidth(20); icon:SetHeight(20)
    icon:SetTexture("Interface\\Icons\\Spell_Nature_WispSplode")
    icon:SetPoint("CENTER", btn, "CENTER", 0, 1)

    local angle = db.minimapAngle or 220
    local function SetPosition(deg)
        local rad = math.rad(deg)
        local x = 80 * math.cos(rad)
        local y = 80 * math.sin(rad)
        btn:ClearAllPoints()
        btn:SetPoint("CENTER", Minimap, "CENTER", x, y)
    end
    SetPosition(angle)

    btn:SetScript("OnDragStart", function() this.dragging = true end)
    btn:SetScript("OnDragStop", function() this.dragging = false end)
    btn:SetScript("OnUpdate", function()
        if not this.dragging then return end
        local mx, my = Minimap:GetCenter()
        local cx, cy = GetCursorPosition()
        local s = Minimap:GetEffectiveScale()
        cx, cy = cx / s, cy / s
        local deg = math.deg(math.atan2(cy - my, cx - mx))
        GetDB().minimapAngle = deg
        SetPosition(deg)
    end)

    btn:SetScript("OnClick", function()
        local mbtn = arg1
        if mbtn == "LeftButton" then
            if not settingsFrame then CreateSettingsFrame() end
            if settingsFrame:IsShown() then settingsFrame:Hide() else settingsFrame:Show() end
        elseif mbtn == "RightButton" then
            local d = GetDB()
            d.mode = (d.mode == "tank") and "dps" or "tank"
            local modeStr = d.mode == "tank" and "|cFF55DD55Tank|r" or "|cFFFF6644DPS/Healer|r"
            DEFAULT_CHAT_FRAME:AddMessage("|cffffff00[amptiePlates]|r Mode: " .. modeStr)
            if settingsUpdateMode then settingsUpdateMode() end
        end
    end)

    btn:SetScript("OnEnter", function()
        GameTooltip:SetOwner(this, "ANCHOR_LEFT")
        GameTooltip:SetText("amptiePlates", 1, 0.82, 0)
        GameTooltip:AddLine("Left-click: Settings", 1, 1, 1)
        GameTooltip:AddLine("Right-click: Toggle Mode", 1, 1, 1)
        GameTooltip:AddLine("Drag: Move button", 0.5, 0.5, 0.5)
        GameTooltip:Show()
    end)
    btn:SetScript("OnLeave", function() GameTooltip:Hide() end)
end

-- ============================================================
-- Slash command
-- ============================================================
SLASH_AMPTIEPLATES1 = "/ap"
SLASH_AMPTIEPLATES2 = "/amptieplates"
SlashCmdList["AMPTIEPLATES"] = function(msg)
    if not settingsFrame then CreateSettingsFrame() end
    if settingsFrame:IsShown() then settingsFrame:Hide() else settingsFrame:Show() end
end

-- ============================================================
-- Init
-- ============================================================
local initFrame = CreateFrame("Frame")
initFrame:RegisterEvent("PLAYER_LOGIN")
initFrame:SetScript("OnEvent", function()
    CreateMinimapButton()

    -- Hook TWThreat to always request per-GUID tank mode data
    if _G.TWT and TWT.UnitDetailedThreatSituation then
        TWT.UnitDetailedThreatSituation = function(limit)
            SendAddonMessage(TWT.UDTS .. "_TM", "limit=" .. limit, TWT.channel)
        end
    end

    -- Compute jitter offset for threat sharing (spread evenly across raid)
    local raidSize = GetNumRaidMembers()
    if raidSize > 0 then
        for i = 1, raidSize do
            local name = GetRaidRosterInfo(i)
            if name == UnitName("player") then
                shareJitter = (i / raidSize) * 0.1  -- small offset within interval
                break
            end
        end
    else
        local partySize = GetNumPartyMembers()
        if partySize > 0 then
            shareJitter = math.random() * 0.1
        end
    end

    -- Detect aura tracking capability
    AP_HAS_LIBDEBUFF = (pfUI and pfUI.libdebuff and pfUI.libdebuff.IterDebuffs ~= nil)
    AP_CAN_TRACK_AURAS = (AP_HAS_LIBDEBUFF or AP_HAS_SUPERWOW)

    -- Hook libdebuff events for dirty-flagging (event-driven aura updates)
    if AP_HAS_LIBDEBUFF then
        local auraFrame = CreateFrame("Frame")
        auraFrame:RegisterEvent("DEBUFF_ADDED_OTHER")
        auraFrame:RegisterEvent("DEBUFF_REMOVED_OTHER")
        auraFrame:SetScript("OnEvent", function()
            local a1 = arg1
            if a1 then auraGuidDirty[a1] = true end
        end)
    end

    local auraStatus = AP_CAN_TRACK_AURAS and (AP_HAS_LIBDEBUFF and "libdebuff" or "GetUnitField") or "disabled"
    DEFAULT_CHAT_FRAME:AddMessage("|cffffff00[amptiePlates]|r v0.2 loaded. Auras: " .. auraStatus .. ". Type /ap for settings.")
end)
