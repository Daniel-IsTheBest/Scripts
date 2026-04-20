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
				if (Enum <= 24) then
					if (Enum <= 11) then
						if (Enum <= 5) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									do
										return;
									end
								elseif (Enum == 1) then
									do
										return;
									end
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 3) then
								VIP = Inst[3];
							elseif (Enum == 4) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
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
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							elseif (Enum == 7) then
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
									if (Mvm[1] == 30) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 9) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 10) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 17) then
						if (Enum <= 14) then
							if (Enum <= 12) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 13) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 15) then
							Stk[Inst[2]] = Stk[Inst[3]];
						elseif (Enum > 16) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A]();
						end
					elseif (Enum <= 20) then
						if (Enum <= 18) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum == 19) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
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
								if (Mvm[1] == 30) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 22) then
						if (Enum > 21) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum == 23) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					end
				elseif (Enum <= 36) then
					if (Enum <= 30) then
						if (Enum <= 27) then
							if (Enum <= 25) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 26) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 28) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 29) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 33) then
						if (Enum <= 31) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 32) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 34) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					elseif (Enum == 35) then
						Stk[Inst[2]] = Inst[3];
					elseif Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 42) then
					if (Enum <= 39) then
						if (Enum <= 37) then
							Stk[Inst[2]] = {};
						elseif (Enum > 38) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 40) then
						Stk[Inst[2]] = Inst[3] ~= 0;
					elseif (Enum > 41) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
					else
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 45) then
					if (Enum <= 43) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Enum == 44) then
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 47) then
					if (Enum == 46) then
						if (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum > 48) then
					Stk[Inst[2]] = Upvalues[Inst[3]];
				else
					local A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!443Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403463Q00682Q7470733A2Q2F6769746875622E636F6D2F462Q6F746167657375732F57696E6455492F72656C65617365732F6C61746573742F646F776E6C6F61642F6D61696E2E6C7561030C3Q0043726561746557696E646F7703053Q005469746C65030B3Q00416D62657220416C65727403043Q0049636F6E03073Q006D6F6E69746F7203063Q00417574686F7203123Q0062792044616E69656C636872697375656F7703043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574025Q00208240025Q00C07C4003073Q004D696E53697A6503073Q00566563746F72322Q033Q006E6577025Q00808140025Q00E0754003073Q004D617853697A65025Q00908A4003093Q00546F2Q676C654B657903043Q00456E756D03073Q004B6579436F646503093Q004C6566745368696674030B3Q005472616E73706172656E742Q0103053Q005468656D6503043Q004461726B03093Q00526573697A61626C65030C3Q00536964654261725769647468026Q006940031B3Q004261636B67726F756E64496D6167655472616E73706172656E637902E17A14AE47E1DA3F030D3Q004869646553656172636842617203103Q005363726F2Q6C426172456E61626C656401002Q033Q0054616703063Q0076312E302E3003053Q00436F6C6F7203063Q00436F6C6F723303073Q0066726F6D48657803073Q002333302Q66366103063Q00526164697573028Q002Q033Q0054616203053Q004C6F2Q627903063Q004C6F636B6564026Q00104003063Q0042752Q746F6E030C3Q0043726561746520506172747903043Q0044657363034Q0003083Q0043612Q6C6261636B03053Q00496E70757403063Q00416D6F756E7403053Q0056616C756503013Q0034030B3Q00506C616365686F6C646572030A3Q00456E746572205465787403043Q0047616D65029A5Q99B93F03063Q00546F2Q676C65030D3Q00436F2Q6C65637420412Q706C6503093Q00287365636F6E64732903013Q003100693Q0012023Q00013Q001202000100023Q00200B000100010003001223000300044Q0005000100034Q002F5Q00022Q00043Q0001000200200B00013Q00052Q000E00033Q000E0030200003000600070030200003000800090030200003000A000B0012020004000D3Q00201800040004000E0012230005000F3Q001223000600104Q00300004000600020010150003000C0004001202000400123Q002018000400040013001223000500143Q001223000600154Q0030000400060002001015000300110004001202000400123Q002018000400040013001223000500173Q001223000600144Q0030000400060002001015000300160004001202000400193Q00201800040004001A00201800040004001B0010150003001800040030200003001C001D0030200003001E001F00302000030020001D00302000030021002200302000030023002400302000030025001D0030200003002600272Q003000010003000200200B0002000100282Q000E00043Q00030030200004000600290012020005002B3Q00201800050005002C0012230006002D4Q001A0005000200020010150004002A00050030200004002E002F2Q001F00020004000100200B0002000100302Q000E00043Q00020030200004000600310030200004003200272Q0030000200040002001223000300333Q00200B0004000200342Q000E00063Q000400302000060006003500302000060036003700302000060032002700061400073Q000100012Q001E3Q00033Q0010150006003800072Q003000040006000200200B0005000200392Q000E00073Q000500302000070006003A0030200007003600370030200007003B003C0030200007003D003E00061400080001000100012Q001E3Q00033Q0010150007003800082Q003000050007000200200B0006000100302Q000E00083Q000200302000080006003F0030200008003200272Q00300006000800022Q001600075Q001223000800403Q00200B0009000600412Q000E000B3Q0004003020000B00060042003020000B00360037003020000B003B0027000614000C0002000100022Q001E3Q00074Q001E3Q00083Q001015000B0038000C2Q00300009000B000200200B000A000600392Q000E000C3Q0005003020000C00060043003020000C00360037003020000C003B0044003020000C003D003E000614000D0003000100012Q001E3Q00083Q001015000C0038000D2Q0030000A000C00026Q00013Q00043Q000A3Q00026Q00F03F03213Q005061727479536572766963652F5265717565737450617274794372656174696F6E027Q004003043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004E6574776F726B030B3Q0052656D6F74654576656E74030A3Q004669726553657276657203063Q00756E7061636B00104Q000E5Q00020030203Q000100022Q002200015Q0010153Q00030001001202000100043Q00200B000100010005001223000300064Q003000010003000200201800010001000700201800010001000800200B0001000100090012020003000A4Q000F00046Q0027000300044Q001B00013Q00016Q00017Q00023Q0003083Q00746F6E756D626572028Q0001093Q001202000100014Q000F00026Q001A0001000200020006240001000800013Q00040D3Q00080001000E0C000200080001000100040D3Q000800012Q002A00019Q0000017Q00023Q0003043Q007461736B03053Q00737061776E010A4Q002A7Q0006243Q000900013Q00040D3Q00090001001202000100013Q00201800010001000200061400023Q000100022Q00318Q00313Q00014Q00290001000200016Q00013Q00013Q000B3Q00026Q00F03F03153Q005475746F7269616C2F436F2Q6C656374412Q706C6503043Q0067616D65030A3Q004765745365727669636503113Q005265706C69636174656453746F7261676503073Q004E6574776F726B030B3Q0052656D6F74654576656E74030A3Q004669726553657276657203063Q00756E7061636B03043Q007461736B03043Q007761697400164Q00227Q0006243Q001500013Q00040D3Q001500012Q000E5Q00010030203Q00010002001202000100033Q00200B000100010004001223000300054Q003000010003000200201800010001000600201800010001000700200B000100010008001202000300094Q000F00046Q0027000300044Q001B00013Q00010012020001000A3Q00201800010001000B2Q0022000200014Q002900010002000100040D5Q00016Q00017Q00023Q0003083Q00746F6E756D626572028Q0001093Q001202000100014Q000F00026Q001A0001000200020006240001000800013Q00040D3Q00080001000E0C000200080001000100040D3Q000800012Q002A00019Q0000017Q00", GetFEnv(), ...);
