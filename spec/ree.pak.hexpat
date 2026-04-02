#pragma author Me together with Codex
#pragma description Dead Rising Deluxe Remaster Demo .pak File
#pragma endian little
#pragma array_limit 1000000
#pragma pattern_limit 100000000


import std.sys ;    // std::assert()
import std.core ;
import std.io ;
import std.string ;


enum Features : s16 {
    NONE                = 0x0000,
    ENCRYPTED_RESOURCES = 0x0001,
    DLC_EXTRA_DATA1     = 0x0003,
    EXTRA_DATA          = 0x0004,
    CHUNKED_RESOURCES   = 0x0008,
    DLC_EXTRA_DATA2     = 0x000B,
};

enum Compression : u8 {
    NONE    = 0,
    DEFLATE = 1,
    ZSTD    = 2,
};

enum Encryption : u8 {
    None         = 0,
    Type_Invalid = 1,
};

fn get_compression( s64 attr ) {
    Compression comp = attr & 0xF ;
    return comp ;
};

fn get_encryption( s64 attr ) {
    Encryption enc = attr >> 16 & 0xFF ;
    return enc ;
};


struct PakEntryV4 {
    u32         m_HashNameLower ;   // Lower 32 bits of filename hash
    u32         m_HashNameUpper ;   // Upper 32 bits of filename hash
    s64         m_Offset ;          // Absolute file offset in PAK
    s64         m_CompressedSize ;  // Compressed size on disk
    s64         m_DecompressedSize ;// Uncompressed size
    s64         m_Attributes ;      // Compression / encryption / chunk flags
    u64         m_Checksum ;        // xxHash64 or Murmur checksum
    
    // just for type check
    u8          m_Data[4] @ m_Offset ;
    
}[[name(PakEntryV4_Name(this))]];

fn PakEntryV4_Name( auto data ) {
    return std::format( "( offset {} : size {} )( {} )( {} )" , 
        data.m_Offset , 
        data.m_CompressedSize , 
        get_compression( data.m_Attributes ) ,
        get_encryption( data.m_Attributes )   
    );
};



struct PakHeader {
    char        m_Magic[4] ;        // 0x414B504B = "KPKA"
    u8          m_MajorVersion ;    // 2 or 4
    u8          m_MinorVersion ;    // 0, 1, or 2
    Features    m_Feature ;         // Feature flags (s16)
    s32         m_TotalFiles ;      // Number of file entries
    u32         m_Fingerprint ;     // Build / fingerprint hash
    
    // only for dead rising deluxe remaster demo
    std::assert( m_MajorVersion == 4, "unsupported major version" ) ;
    std::assert( m_MinorVersion == 1, "unsupported minor version" ) ;
    std::assert( m_TotalFiles != 0, "there are no assets" ) ;

}[[name(PakHeader_Name(this))]];

fn PakHeader_Name( auto data ) {
    return std::format( "m_Header ( feature : {} )" ,
        data.m_Feature 
    );
};


struct PakFile {

    PakHeader   m_Header ;
    
    if ( m_Header.m_Feature == Features::NONE ) {
        PakEntryV4  m_Assets[ m_Header.m_TotalFiles ] ;
    }
    else if ( m_Header.m_Feature == Features::EXTRA_DATA ) {
        PakEntryV4  m_Assets[ m_Header.m_TotalFiles ] ;
        u8      m_Padding[4] ;
        u8      m_Key[128] ;
    } 
    else if ( m_Header.m_Feature == Features::DLC_EXTRA_DATA1 ||
              m_Header.m_Feature == Features::DLC_EXTRA_DATA2 ) {
        PakEntryV4  m_Assets[ m_Header.m_TotalFiles ] ;
        u8      m_Padding[9] ;
        u8      m_Key[128] ;
    } 
    else if ( m_Header.m_Feature == Features::ENCRYPTED_RESOURCES ||
              m_Header.m_Feature == Features::CHUNKED_RESOURCES ) {
        // The entry table is stored first and a 128-byte encrypted key follows it.
        // In REE-Lib the key itself is RSA-decoded before the entry bytes are XOR-decoded.
        // Pure ImHex Pattern Language can generate transformed sections, but the RSA step
        // here uses a 128-byte modulus, so the decrypted table is not reconstructed inline.
        u8      m_EncryptedAssets[ m_Header.m_TotalFiles * 48 ] ;
        u8      m_Key[128] ;
    }

}[[name(PakFile_Name(this))]];

fn PakFile_Name( auto data ) {
    return std::format("( fourcc:{} )( ver:{}.{} )( assets:{} )",
        data.m_Header.m_Magic ,
        data.m_Header.m_MajorVersion ,
        data.m_Header.m_MinorVersion ,
        data.m_Header.m_TotalFiles 
    );
};


PakFile pak @ 0x00;
