--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.9) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 28) then
					if (Enum <= 13) then
						if (Enum <= 6) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif (Enum == 1) then
									local A = Inst[2];
									local C = Inst[4];
									local CB = A + 2;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[1];
									if R then
										Stk[CB] = R;
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum <= 4) then
								if (Enum > 3) then
									Stk[Inst[2]] = Inst[3];
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 5) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A]();
							end
						elseif (Enum <= 9) then
							if (Enum <= 7) then
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 36) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							elseif (Enum > 8) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 11) then
							if (Enum == 10) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum > 12) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 36) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 20) then
						if (Enum <= 16) then
							if (Enum <= 14) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Enum > 15) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 18) then
							if (Enum > 17) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum > 19) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 24) then
						if (Enum <= 22) then
							if (Enum == 21) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 23) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 26) then
						if (Enum > 25) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum == 27) then
						VIP = Inst[3];
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 42) then
					if (Enum <= 35) then
						if (Enum <= 31) then
							if (Enum <= 29) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Enum == 30) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum <= 33) then
							if (Enum > 32) then
								do
									return;
								end
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum > 34) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 38) then
						if (Enum <= 36) then
							Stk[Inst[2]] = Stk[Inst[3]];
						elseif (Enum > 37) then
							do
								return;
							end
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 40) then
						if (Enum == 39) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum > 41) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 49) then
					if (Enum <= 45) then
						if (Enum <= 43) then
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum == 44) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 47) then
						if (Enum == 46) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum == 48) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						Stk[Inst[2]] = {};
					end
				elseif (Enum <= 53) then
					if (Enum <= 51) then
						if (Enum == 50) then
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum > 52) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 55) then
					if (Enum == 54) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
					elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum > 56) then
					local A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Inst[3]));
				else
					Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!4E3Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403463Q00682Q7470733A2Q2F6769746875622E636F6D2F462Q6F746167657375732F57696E6455492F72656C65617365732F6C61746573742F646F776E6C6F61642F6D61696E2E6C7561030C3Q0043726561746557696E646F7703053Q005469746C65030B3Q00416D62657220416C65727403043Q0049636F6E03073Q006D6F6E69746F7203063Q00417574686F7203123Q0062792044616E69656C636872697375656F7703043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574025Q00208240025Q00C07C4003073Q004D696E53697A6503073Q00566563746F72322Q033Q006E6577025Q00808140025Q00E0754003073Q004D617853697A65025Q00908A4003093Q00546F2Q676C654B657903043Q00456E756D03073Q004B6579436F646503093Q004C6566745368696674030B3Q005472616E73706172656E742Q0103053Q005468656D6503043Q004461726B03093Q00526573697A61626C65030C3Q00536964654261725769647468026Q006940031B3Q004261636B67726F756E64496D6167655472616E73706172656E637902E17A14AE47E1DA3F030D3Q004869646553656172636842617203103Q005363726F2Q6C426172456E61626C656401002Q033Q0054616703063Q0076312E302E3003053Q00436F6C6F7203063Q00436F6C6F723303073Q0066726F6D48657803073Q002333302Q66366103063Q00526164697573028Q002Q033Q0054616203053Q004C6F2Q627903063Q004C6F636B6564026Q00104003063Q0042752Q746F6E030C3Q0043726561746520506172747903043Q0044657363034Q0003083Q0043612Q6C6261636B03053Q00496E70757403063Q00416D6F756E7403053Q0056616C756503013Q0034030B3Q00506C616365686F6C646572030A3Q00456E746572205465787403043Q0047616D65029A5Q99B93F03063Q00546F2Q676C65030D3Q00436F2Q6C65637420412Q706C6503093Q00287365636F6E64732903013Q0031030B3Q004C6F63616C506C6179657203053Q0053702Q656403023Q00313603043Q005479706503093Q004A756D2Q706F77657203023Q003530030C3Q00466972737420506572736F6E030C3Q00546869726420506572736F6E03163Q00496E7374616E7450726F78696D69747950726F6D707403063Q004E6F636C697000A33Q0012223Q00013Q001222000100023Q00201100010001000300122F000300044Q0014000100034Q00025Q00022Q001E3Q0001000200201100013Q00052Q002800033Q000E002Q30000300060007002Q30000300080009002Q300003000A000B0012220004000D3Q00201D00040004000E00122F0005000F3Q00122F000600104Q000D0004000600020010190003000C0004001222000400123Q00201D00040004001300122F000500143Q00122F000600154Q000D000400060002001019000300110004001222000400123Q00201D00040004001300122F000500173Q00122F000600144Q000D000400060002001019000300160004001222000400193Q00201D00040004001A00201D00040004001B001019000300180004002Q300003001C001D002Q300003001E001F002Q3000030020001D002Q30000300210022002Q30000300230024002Q3000030025001D002Q300003002600272Q000D0001000300020020110002000100282Q002800043Q0003002Q300004000600290012220005002B3Q00201D00050005002C00122F0006002D4Q00340005000200020010190004002A0005002Q300004002E002F2Q00290002000400010020110002000100302Q002800043Q0002002Q30000400060031002Q300004003200272Q000D00020004000200122F000300333Q0020110004000200342Q002800063Q0004002Q30000600060035002Q30000600360037002Q3000060032002700060C00073Q000100012Q00243Q00033Q0010190006003800072Q000D0004000600020020110005000200392Q002800073Q0005002Q3000070006003A002Q30000700360037002Q300007003B003C002Q300007003D003E00060C00080001000100012Q00243Q00033Q0010190007003800082Q000D0005000700020020110006000100302Q002800083Q0002002Q3000080006003F002Q300008003200272Q000D0006000800022Q001000075Q00122F000800403Q0020110009000600412Q0028000B3Q0004002Q30000B00060042002Q30000B00360037002Q30000B003B002700060C000C0002000100022Q00243Q00074Q00243Q00083Q001019000B0038000C2Q000D0009000B0002002011000A000600392Q0028000C3Q0005002Q30000C00060043002Q30000C00360037002Q30000C003B0044002Q30000C003D003E00060C000D0003000100012Q00243Q00083Q001019000C0038000D2Q000D000A000C0002002011000B000100302Q0028000D3Q0002002Q30000D00060045002Q30000D003200272Q000D000B000D0002002011000C000B00392Q0028000E3Q0006002Q30000E00060046002Q30000E00360037002Q30000E003B0047002Q30000E00480039002Q30000E003D003E000238000F00043Q001019000E0038000F2Q000D000C000E0002002011000D000B00392Q0028000F3Q0006002Q30000F00060049002Q30000F00360037002Q30000F003B004A002Q30000F00480039002Q30000F003D003E000238001000053Q001019000F003800102Q000D000D000F0002002011000E000B00342Q002800103Q0004002Q3000100006004B002Q30001000360037002Q30001000320027000238001100063Q0010190010003800112Q000D000E00100002002011000F000B00342Q002800113Q0004002Q3000110006004C002Q30001100360037002Q30001100320027000238001200073Q0010190011003800122Q000D000F001100020020110010000B00342Q002800123Q0004002Q3000120006004D002Q30001200360037002Q30001200320027000238001300083Q0010190012003800132Q000D0010001200020020110011000B00412Q002800133Q0005002Q3000130006004E002Q30001300360037002Q30001300480041002Q300013003B0027000238001400093Q0010190013003800142Q000D0011001300022Q00213Q00013Q000A3Q000A3Q00026Q00F03F03213Q005061727479536572766963652F5265717565737450617274794372656174696F6E027Q004003043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004E6574776F726B030B3Q0052656D6F74654576656E74030A3Q004669726553657276657203063Q00756E7061636B00104Q00285Q0002002Q303Q000100022Q002C00015Q0010193Q00030001001222000100043Q00201100010001000500122F000300064Q000D00010003000200201D00010001000700201D0001000100080020110001000100090012220003000A4Q003200046Q0005000300044Q001200013Q00012Q00213Q00017Q00023Q0003083Q00746F6E756D626572028Q0001093Q001222000100014Q003200026Q00340001000200020006160001000800013Q00042D3Q00080001000E18000200080001000100042D3Q000800012Q001A00016Q00213Q00017Q00023Q0003043Q007461736B03053Q00737061776E010A4Q001A7Q0006163Q000900013Q00042D3Q00090001001222000100013Q00201D00010001000200060C00023Q000100022Q00258Q00253Q00014Q00230001000200012Q00213Q00013Q00013Q000B3Q00026Q00F03F03153Q005475746F7269616C2F436F2Q6C656374412Q706C6503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004E6574776F726B030B3Q0052656D6F74654576656E74030A3Q004669726553657276657203063Q00756E7061636B03043Q007461736B03043Q007761697400164Q002C7Q0006163Q001500013Q00042D3Q001500012Q00285Q0001002Q303Q00010002001222000100033Q00201100010001000400122F000300054Q000D00010003000200201D00010001000600201D000100010007002011000100010008001222000300094Q003200046Q0005000300044Q001200013Q00010012220001000A3Q00201D00010001000B2Q002C000200014Q002300010002000100042D5Q00012Q00213Q00017Q00023Q0003083Q00746F6E756D626572028Q0001093Q001222000100014Q003200026Q00340001000200020006160001000800013Q00042D3Q00080001000E18000200080001000100042D3Q000800012Q001A00016Q00213Q00017Q00063Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q0043686172616374657203083Q0048756D616E6F696403093Q0057616C6B53702Q656401073Q001222000100013Q00201D00010001000200201D00010001000300201D00010001000400201D000100010005001019000100064Q00213Q00017Q00063Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q0043686172616374657203083Q0048756D616E6F696403093Q004A756D70506F77657201073Q001222000100013Q00201D00010001000200201D00010001000300201D00010001000400201D000100010005001019000100064Q00213Q00017Q00073Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C61796572030A3Q0043616D6572614D6F646503043Q00456E756D030F3Q004C6F636B4669727374506572736F6E03073Q00436C612Q73696300133Q0012223Q00013Q00201D5Q000200201D5Q000300201D00013Q0004001222000200053Q00201D00020002000400201D0002000200060006090001000E0001000200042D3Q000E0001001222000100053Q00201D00010001000400201D0001000100070010193Q0004000100042D3Q00120001001222000100053Q00201D00010001000400201D0001000100060010193Q000400012Q00213Q00017Q00063Q0003043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C61796572030A3Q0043616D6572614D6F646503043Q00456E756D03073Q00436C612Q73696300083Q0012223Q00013Q00201D5Q000200201D5Q0003001222000100053Q00201D00010001000400201D0001000100060010193Q000400012Q00213Q00017Q00023Q0003043Q007461736B03053Q00737061776E00053Q0012223Q00013Q00201D5Q000200023800016Q00233Q000200012Q00213Q00013Q00013Q00073Q0003063Q0069706169727303043Q0067616D65030E3Q0047657444657363656E64616E74732Q033Q00497341030F3Q0050726F78696D69747950726F6D7074030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E65637400183Q0002387Q001222000100013Q001222000200023Q0020110002000200032Q0005000200034Q000A00013Q000300042D3Q000F000100201100060005000400122F000800054Q000D0006000800020006160006000F00013Q00042D3Q000F00012Q003200066Q0032000700054Q0023000600020001000601000100070001000200042D3Q00070001001222000100023Q00201D00010001000600201100010001000700060C00030001000100012Q00248Q00290001000300012Q00213Q00013Q00023Q00013Q0003053Q007063612Q6C01053Q001222000100013Q00060C00023Q000100012Q00248Q00230001000200012Q00213Q00013Q00013Q00043Q00030C3Q00486F6C644475726174696F6E028Q0003133Q0052657175697265734C696E654F665369676874012Q00054Q002C7Q002Q303Q000100022Q002C7Q002Q303Q000300042Q00213Q00017Q00023Q002Q033Q00497341030F3Q0050726F78696D69747950726F6D707401093Q00201100013Q000100122F000300024Q000D0001000300020006160001000800013Q00042D3Q000800012Q002C00016Q003200026Q00230001000200012Q00213Q00017Q00043Q0003023Q005F4703063Q004E6F636C697003043Q007461736B03053Q00737061776E01093Q001222000100013Q001019000100023Q0006163Q000800013Q00042D3Q00080001001222000100033Q00201D00010001000400023800026Q00230001000200012Q00213Q00013Q00013Q000E3Q0003023Q005F4703063Q004E6F636C697003043Q007461736B03043Q007761697403043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q0043686172616374657203063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465012Q001E3Q0012223Q00013Q00201D5Q00020006163Q001D00013Q00042D3Q001D00010012223Q00033Q00201D5Q00042Q001E3Q000100020006163Q001D00013Q00042D3Q001D00010012223Q00053Q00201D5Q000600201D5Q000700201D5Q00080006165Q00013Q00042D5Q0001001222000100093Q00201100023Q000A2Q0005000200034Q000A00013Q000300042D3Q001A000100201100060005000B00122F0008000C4Q000D0006000800020006160006001A00013Q00042D3Q001A0001002Q300005000D000E000601000100140001000200042D3Q0014000100042D5Q00012Q00213Q00017Q00", GetFEnv(), ...);
