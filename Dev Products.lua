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
				if (Enum <= 31) then
					if (Enum <= 15) then
						if (Enum <= 7) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum == 0) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
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
											if (Mvm[1] == 61) then
												Indexes[Idx - 1] = {Stk,Mvm[3]};
											else
												Indexes[Idx - 1] = {Upvalues,Mvm[3]};
											end
											Lupvals[#Lupvals + 1] = Indexes;
										end
										Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
									end
								elseif (Enum == 2) then
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
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								end
							elseif (Enum <= 5) then
								if (Enum == 4) then
									if not Stk[Inst[2]] then
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
							elseif (Enum == 6) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								Stk[Inst[2]] = {};
							end
						elseif (Enum <= 11) then
							if (Enum <= 9) then
								if (Enum > 8) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 10) then
								do
									return;
								end
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 13) then
							if (Enum > 12) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum == 14) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 23) then
						if (Enum <= 19) then
							if (Enum <= 17) then
								if (Enum == 16) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum > 18) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 21) then
							if (Enum == 20) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								VIP = Inst[3];
							end
						elseif (Enum > 22) then
							Upvalues[Inst[3]] = Stk[Inst[2]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						end
					elseif (Enum <= 27) then
						if (Enum <= 25) then
							if (Enum == 24) then
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
									if (Mvm[1] == 61) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum == 26) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 29) then
						if (Enum > 28) then
							Stk[Inst[2]] = {};
						else
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum == 30) then
						VIP = Inst[3];
					else
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					end
				elseif (Enum <= 47) then
					if (Enum <= 39) then
						if (Enum <= 35) then
							if (Enum <= 33) then
								if (Enum == 32) then
									Upvalues[Inst[3]] = Stk[Inst[2]];
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum == 34) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum <= 37) then
							if (Enum == 36) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 38) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 43) then
						if (Enum <= 41) then
							if (Enum == 40) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							else
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							end
						elseif (Enum == 42) then
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
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 45) then
						if (Enum > 44) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum > 46) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					else
						Stk[Inst[2]] = Inst[3] ~= 0;
					end
				elseif (Enum <= 55) then
					if (Enum <= 51) then
						if (Enum <= 49) then
							if (Enum == 48) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								do
									return;
								end
							end
						elseif (Enum > 50) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						end
					elseif (Enum <= 53) then
						if (Enum == 52) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum == 54) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					else
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 59) then
					if (Enum <= 57) then
						if (Enum == 56) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum == 58) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 61) then
					if (Enum == 60) then
						do
							return Stk[Inst[2]];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 62) then
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
				elseif (Enum > 63) then
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
				elseif not Stk[Inst[2]] then
					VIP = VIP + 1;
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!383Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403463Q00682Q7470733A2Q2F6769746875622E636F6D2F462Q6F746167657375732F57696E6455492F72656C65617365732F6C61746573742F646F776E6C6F61642F6D61696E2E6C7561030C3Q0043726561746557696E646F7703053Q005469746C65030C3Q004465762050726F647563747303063Q00417574686F7203123Q0062792044616E69656C636872697375656F7703043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574025Q00208240025Q00C07C4003073Q004D696E53697A6503073Q00566563746F72322Q033Q006E6577025Q00808140025Q00E0754003073Q004D617853697A65025Q00908A4003093Q00546F2Q676C654B657903043Q00456E756D03073Q004B6579436F646503093Q004C6566745368696674030B3Q005472616E73706172656E742Q0103053Q005468656D6503043Q004461726B03093Q00526573697A61626C65030C3Q00536964654261725769647468026Q006940031B3Q004261636B67726F756E64496D6167655472616E73706172656E637902E17A14AE47E1DA3F030D3Q004869646553656172636842617203103Q005363726F2Q6C426172456E61626C6564010003043Q005573657203073Q00456E61626C656403093Q00416E6F6E796D6F757303083Q0043612Q6C6261636B2Q033Q0054616203083Q0050726F647563747303063Q004C6F636B6564030A3Q004765745365727669636503123Q004D61726B6574706C6163655365727669636503073Q00506C617965727303083Q0044726F70646F776E030E3Q0053656C6563742050726F6475637403043Q0044657363034Q0003063Q0056616C75657303053Q0056616C756503063Q0042752Q746F6E030B3Q004275792050726F6475637403073Q005265667265736800633Q0012213Q00013Q001221000100023Q00202D00010001000300120C000300044Q0005000100034Q00365Q00022Q00283Q0001000200202D00013Q00052Q001D00033Q000E0030330003000600070030330003000800090012210004000B3Q00204000040004000C00120C0005000D3Q00120C0006000E4Q001A0004000600020010270003000A0004001221000400103Q00204000040004001100120C000500123Q00120C000600134Q001A0004000600020010270003000F0004001221000400103Q00204000040004001100120C000500153Q00120C000600124Q001A000400060002001027000300140004001221000400173Q0020400004000400180020400004000400190010270003001600040030330003001A001B0030330003001C001D0030330003001E001B0030330003001F002000303300030021002200303300030023001B0030330003002400252Q001D00043Q000300303300040027001B00303300040028002500022900055Q0010270004002900050010270003002600042Q001A00010003000200202D00020001002A2Q001D00043Q000200303300040006002B0030330004002C00252Q001A000200040002001221000300023Q00202D00030003002D00120C0005002E4Q001A000300050002001221000400023Q00202D00040004002D00120C0006002F4Q001A0004000600022Q001D00056Q001B000600063Q00061900070001000100022Q003D3Q00054Q003D3Q00034Q003B000800074Q002800080001000200202D0009000200302Q001D000B3Q0005003033000B00060031003033000B00320033001027000B00340008003033000B00350033000619000C0002000100022Q003D3Q00064Q003D3Q00053Q001027000B0029000C2Q001A0009000B000200202D000A000200362Q001D000C3Q0004003033000C00060037003033000C00320033003033000C002C0025000619000D0003000100032Q003D3Q00064Q003D3Q00044Q003D3Q00033Q001027000C0029000D2Q001A000A000C000200202D000B000200362Q001D000D3Q0004003033000D00060038003033000D00320033003033000D002C0025000619000E0004000100012Q003D3Q00073Q001027000D0029000E2Q0013000B000D00012Q000A3Q00013Q00058Q00014Q000A3Q00017Q000B3Q0003053Q007063612Q6C030E3Q0047657443752Q72656E745061676503063Q0069706169727303043Q004E616D65030F3Q00556E6B6E6F776E2050726F6475637403093Q0050726F64756374496403053Q007461626C6503063Q00696E73657274030A3Q00497346696E697368656403163Q00416476616E6365546F4E657874506167654173796E6303043Q00736F7274002F4Q001D8Q00178Q001D7Q001221000100013Q00061900023Q000100012Q00383Q00014Q000800010002000200063A0001000B00013Q0004153Q000B00010006040002000D000100010004153Q000D00012Q001D00036Q003C000300023Q00202D0003000200022Q000F000300020002001221000400034Q003B000500034Q00080004000200060004153Q0020000100204000090008000400060400090017000100010004153Q0017000100120C000900053Q002040000A000800062Q003B000B00096Q000C6Q0034000C000B000A001221000C00073Q002040000C000C00082Q003B000D6Q003B000E000B4Q0013000C000E000100062A00040013000100020004153Q0013000100204000040002000900063A0004002600013Q0004153Q002600010004153Q0029000100202D00040002000A2Q00370004000200010004153Q000D0001001221000300073Q00204000030003000B2Q003B00046Q00370003000200012Q003C3Q00024Q000A3Q00013Q00013Q00013Q0003193Q00476574446576656C6F70657250726F64756374734173796E6300059Q003Q00202D5Q00012Q00393Q00014Q00098Q000A3Q00019Q002Q0001046Q000100014Q001F000100014Q001700016Q000A3Q00017Q00033Q00030B3Q004C6F63616C506C6179657203233Q005369676E616C50726F6D707450726F64756374507572636861736546696E697368656403063Q00557365724964000E9Q003Q0006043Q0004000100010004153Q000400012Q000A3Q00018Q00013Q0020405Q00014Q00018Q000200023Q00202D00020002000200204000043Q00032Q003B000500014Q002E000600014Q00130002000600012Q000A3Q00019Q003Q00039Q004Q00283Q000100022Q000A3Q00017Q00", GetFEnv(), ...);
