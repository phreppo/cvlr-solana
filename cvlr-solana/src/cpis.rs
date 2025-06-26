use super::token::spl_token_account_get_amount;
use cvlr_asserts::*;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    entrypoint::ProgramResult,
    instruction::{AccountMeta, Instruction},
    program_error::ProgramError,
    pubkey::Pubkey,
};

/// Creates a `Transfer` instruction.
#[cvlr_early_panic::early_panic]
#[inline]
pub fn transfer(
    token_program_id: &Pubkey,
    source_pubkey: &Pubkey,
    destination_pubkey: &Pubkey,
    authority_pubkey: &Pubkey,
    signer_pubkeys: &[&Pubkey],
    amount: u64,
) -> Result<Instruction, ProgramError> {
    spl_token::check_program_account(token_program_id).unwrap();
    let data = spl_token::instruction::TokenInstruction::Transfer { amount }.pack();

    let mut accounts = Vec::with_capacity(3 + signer_pubkeys.len());
    accounts.push(AccountMeta::new(*source_pubkey, false));
    accounts.push(AccountMeta::new(*destination_pubkey, false));
    accounts.push(AccountMeta::new_readonly(
        *authority_pubkey,
        signer_pubkeys.is_empty(),
    ));
    for signer_pubkey in signer_pubkeys.iter() {
        accounts.push(AccountMeta::new_readonly(**signer_pubkey, true));
    }

    let pubkey = write_spl_token_pubkey();
    Ok(Instruction {
        program_id: pubkey,
        accounts,
        data,
    })
}

/// Creates a `MintTo` instruction.
pub fn mint_to(
    token_program_id: &Pubkey,
    mint_pubkey: &Pubkey,
    account_pubkey: &Pubkey,
    owner_pubkey: &Pubkey,
    signer_pubkeys: &[&Pubkey],
    amount: u64,
) -> Result<Instruction, ProgramError> {
    spl_token::check_program_account(token_program_id)?;
    let data = spl_token::instruction::TokenInstruction::MintTo { amount }.pack();

    let mut accounts = Vec::with_capacity(3 + signer_pubkeys.len());
    accounts.push(AccountMeta::new(*mint_pubkey, false));
    accounts.push(AccountMeta::new(*account_pubkey, false));
    accounts.push(AccountMeta::new_readonly(
        *owner_pubkey,
        signer_pubkeys.is_empty(),
    ));
    for signer_pubkey in signer_pubkeys.iter() {
        accounts.push(AccountMeta::new_readonly(**signer_pubkey, true));
    }

    let pubkey = write_spl_token_pubkey();
    Ok(Instruction {
        program_id: pubkey,
        accounts,
        data,
    })
}

/// Creates a `Burn` instruction.
pub fn burn(
    token_program_id: &Pubkey,
    account_pubkey: &Pubkey,
    mint_pubkey: &Pubkey,
    authority_pubkey: &Pubkey,
    signer_pubkeys: &[&Pubkey],
    amount: u64,
) -> Result<Instruction, ProgramError> {
    spl_token::check_program_account(token_program_id)?;
    let data = spl_token::instruction::TokenInstruction::Burn { amount }.pack();

    let mut accounts = Vec::with_capacity(3 + signer_pubkeys.len());
    accounts.push(AccountMeta::new(*account_pubkey, false));
    accounts.push(AccountMeta::new(*mint_pubkey, false));
    accounts.push(AccountMeta::new_readonly(
        *authority_pubkey,
        signer_pubkeys.is_empty(),
    ));
    for signer_pubkey in signer_pubkeys.iter() {
        accounts.push(AccountMeta::new_readonly(**signer_pubkey, true));
    }

    let pubkey = write_spl_token_pubkey();
    Ok(Instruction {
        program_id: pubkey,
        accounts,
        data,
    })
}

/// Creates a `CloseAccount` instruction.
#[cvlr_early_panic::early_panic]
pub fn close_account(
    token_program_id: &Pubkey,
    account_pubkey: &Pubkey,
    destination_pubkey: &Pubkey,
    owner_pubkey: &Pubkey,
    signer_pubkeys: &[&Pubkey],
) -> Result<Instruction, ProgramError> {
    spl_token::check_program_account(token_program_id)?;
    // Currently, we cannot use `pack` directly because the PTA analysis in the
    // Certora Prover is not precise enough to handle the case in which the
    // instruction does not carry any data.
    // let data = spl_token::instruction::TokenInstruction::CloseAccount.pack();
    let data = pack_close_account();

    let mut accounts = Vec::with_capacity(3 + signer_pubkeys.len());
    accounts.push(AccountMeta::new(*account_pubkey, false));
    accounts.push(AccountMeta::new(*destination_pubkey, false));
    accounts.push(AccountMeta::new_readonly(
        *owner_pubkey,
        signer_pubkeys.is_empty(),
    ));
    for signer_pubkey in signer_pubkeys.iter() {
        accounts.push(AccountMeta::new_readonly(**signer_pubkey, true));
    }

    let pubkey = write_spl_token_pubkey();
    Ok(Instruction {
        program_id: pubkey,
        accounts,
        data,
    })
}

/// Mock for `spl_token::instruction::TokenInstruction::CloseAccount.pack()`.
fn pack_close_account() -> Vec<u8> {
    let mut buf = Vec::with_capacity(9); // 1 byte for the instruction discriminant and 8 bytes of padding.
    let padding: u64 = 0;
    buf.push(9); // 9 is `CloseAccount` discriminant.

    // We extend the buffer with 8 bytes so that the Certora Prover can
    // correctly recognize the token instruction.
    buf.extend_from_slice(&padding.to_le_bytes()); // 8 bytes of padding
    buf
}

/// Creates a `TransferChecked` instruction.
#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn transfer_checked(
    token_program_id: &Pubkey,
    source_pubkey: &Pubkey,
    mint_pubkey: &Pubkey,
    destination_pubkey: &Pubkey,
    authority_pubkey: &Pubkey,
    signer_pubkeys: &[&Pubkey],
    amount: u64,
    decimals: u8,
) -> Result<Instruction, ProgramError> {
    // The following is copied by the `spl_token::instruction::transfer_checked` function.
    spl_token::check_program_account(token_program_id)?;
    let data =
        spl_token::instruction::TokenInstruction::TransferChecked { amount, decimals }.pack();

    let mut accounts = Vec::with_capacity(4 + signer_pubkeys.len());
    accounts.push(AccountMeta::new(*source_pubkey, false));
    accounts.push(AccountMeta::new_readonly(*mint_pubkey, false));
    accounts.push(AccountMeta::new(*destination_pubkey, false));
    accounts.push(AccountMeta::new_readonly(
        *authority_pubkey,
        signer_pubkeys.is_empty(),
    ));
    for signer_pubkey in signer_pubkeys.iter() {
        accounts.push(AccountMeta::new_readonly(**signer_pubkey, true));
    }

    let pubkey = write_spl_token_pubkey();
    Ok(Instruction {
        program_id: pubkey,
        accounts,
        data,
    })
}

/// Writes the Pubkey of the `spl_token::id()` directly into a `Pubkey` and
/// returns it. This is used to ensure that the Certora Prover can
/// recognize the `spl_token` program ID when analyzing the CPI invocations.
fn write_spl_token_pubkey() -> Pubkey {
    let mut pubkey = Pubkey::new(&[0u8; 32]);
    unsafe {
        // Get a mutable pointer to the first byte.
        let ptr = &mut pubkey as *mut Pubkey as *mut u64;
        // Write u64s directly. The following corresponds to the Pubkey of the
        // `spl_token::id()`.
        *ptr.add(0) = 10637895772709248262u64;
        *ptr.add(1) = 12428223917890587609u64;
        *ptr.add(2) = 10463932726783620124u64;
        *ptr.add(3) = 12178014311288245306u64;
    }
    pubkey
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_transfer(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
) -> ProgramResult {
    cvlr_assert!(account_infos.len() == 3);
    cvlr_invoke_signed_transfer(instruction, account_infos, &[])
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_signed_transfer(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
    _signers_seeds: &[&[&[u8]]],
) -> ProgramResult {
    cvlr_assert!(account_infos.len() >= 3);
    cvlr_assert!(instruction.data.len() > 0);
    cvlr_assert!(instruction.accounts[0].pubkey == *account_infos[0].key);
    cvlr_assert!(instruction.accounts[1].pubkey == *account_infos[1].key);
    cvlr_assert!(instruction.accounts[2].pubkey == *account_infos[2].key);
    let src_info = &account_infos[0];
    let dst_info = &account_infos[1];
    let authority_info = &account_infos[2];
    let amount = u64::from_le_bytes(instruction.data[1..9].try_into().unwrap());
    super::token::spl_token_transfer(src_info, dst_info, authority_info, amount)
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_mint_to(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
) -> ProgramResult {
    cvlr_assert!(account_infos.len() == 3);
    cvlr_invoke_signed_mint_to(instruction, account_infos, &[])
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_signed_mint_to(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
    _signers_seeds: &[&[&[u8]]],
) -> ProgramResult {
    cvlr_assert!(account_infos.len() >= 3);
    cvlr_assert!(instruction.data.len() > 0);
    cvlr_assert!(instruction.accounts[0].pubkey == *account_infos[0].key);
    cvlr_assert!(instruction.accounts[1].pubkey == *account_infos[1].key);
    cvlr_assert!(instruction.accounts[2].pubkey == *account_infos[2].key);
    let mint_info = &account_infos[0];
    let dst_info = &account_infos[1];
    let authority_info = &account_infos[2];
    let amount = u64::from_le_bytes(instruction.data[1..9].try_into().unwrap());
    super::token::spl_mint_to(mint_info, dst_info, authority_info, amount)
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_burn(instruction: &Instruction, account_infos: &[AccountInfo]) -> ProgramResult {
    cvlr_assert!(account_infos.len() == 3);
    cvlr_invoke_signed_burn(instruction, account_infos, &[])
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_signed_burn(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
    _signers_seeds: &[&[&[u8]]],
) -> ProgramResult {
    cvlr_assert!(account_infos.len() >= 3);
    cvlr_assert!(instruction.data.len() > 0);
    cvlr_assert!(instruction.accounts[0].pubkey == *account_infos[0].key);
    cvlr_assert!(instruction.accounts[1].pubkey == *account_infos[1].key);
    cvlr_assert!(instruction.accounts[2].pubkey == *account_infos[2].key);
    let src_info = &account_infos[0];
    let mint_info = &account_infos[1];
    let authority_info = &account_infos[2];
    let amount = u64::from_le_bytes(instruction.data[1..9].try_into().unwrap());
    super::token::spl_burn(mint_info, src_info, authority_info, amount)
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_close_account(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
) -> ProgramResult {
    cvlr_assert!(account_infos.len() == 3);
    cvlr_invoke_signed_close_account(instruction, account_infos, &[])
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_signed_close_account(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
    _signers_seeds: &[&[&[u8]]],
) -> ProgramResult {
    cvlr_assert!(account_infos.len() >= 3);
    cvlr_assert!(instruction.data.len() > 0);
    cvlr_assert!(instruction.accounts[0].pubkey == *account_infos[0].key);
    cvlr_assert!(instruction.accounts[1].pubkey == *account_infos[1].key);
    cvlr_assert!(instruction.accounts[2].pubkey == *account_infos[2].key);
    let account_info = &account_infos[0];
    let dest_info = &account_infos[1];
    let owner_info = &account_infos[2];
    super::token::spl_close_account(account_info, dest_info, owner_info)
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_transfer_checked(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
) -> ProgramResult {
    cvlr_assert!(account_infos.len() == 4);
    cvlr_invoke_signed_transfer_checked(instruction, account_infos, &[])
}

#[inline(never)]
#[cvlr_early_panic::early_panic]
pub fn cvlr_invoke_signed_transfer_checked(
    instruction: &Instruction,
    account_infos: &[AccountInfo],
    _signers_seeds: &[&[&[u8]]],
) -> ProgramResult {
    cvlr_assert!(account_infos.len() >= 4);
    cvlr_assert!(instruction.data.len() > 0);
    cvlr_assert!(instruction.accounts[0].pubkey == *account_infos[0].key);
    cvlr_assert!(instruction.accounts[1].pubkey == *account_infos[1].key);
    cvlr_assert!(instruction.accounts[2].pubkey == *account_infos[2].key);
    cvlr_assert!(instruction.accounts[3].pubkey == *account_infos[3].key);
    let src_info = &account_infos[0];
    let dst_info = &account_infos[2];
    let authority_info = &account_infos[3];
    let amount = u64::from_le_bytes(instruction.data[1..9].try_into().unwrap());
    super::token::spl_token_transfer(src_info, dst_info, authority_info, amount)
}

#[macro_export]
macro_rules! cvlr_solana_init {
    () => {
        cvlr_solana::cvlr_solana_init!(init_cvlr_solana);
    };

    ($wrapper_name:ident) => {
        #[no_mangle]
        pub fn $wrapper_name() {
            use cvlr_solana::cpis::*;
            rule_to_compile_transfer();
            rule_to_compile_mint_to();
            rule_to_compile_burn();
            rule_to_compile_close_account();
            rule_to_compile_transfer_checked();
        }
    };
}

pub fn rule_to_compile_transfer() {
    let account_infos = super::cvlr_deserialize_nondet_accounts();
    let account_info_iter = &mut account_infos.iter();
    let token_program: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let from: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let to: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let _authority: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let amount: u64 = cvlr_nondet::nondet();
    let decimals: u8 = cvlr_nondet::nondet();
    let mut token_instruction_data = Vec::new();
    token_instruction_data.extend_from_slice(&amount.to_le_bytes());
    token_instruction_data.extend_from_slice(&decimals.to_le_bytes());
    cvlr_assume!(from.key != to.key);
    let from_wallet_amount_pre = spl_token_account_get_amount(from);
    let to_wallet_amount_pre = spl_token_account_get_amount(to);
    process_transfer(&account_infos, &token_instruction_data).unwrap();
    let from_wallet_amount_post = spl_token_account_get_amount(from);
    let to_wallet_amount_post = spl_token_account_get_amount(to);
    cvlr_assert!(*token_program.key == spl_token::id());
    cvlr_assert!(from_wallet_amount_post == from_wallet_amount_pre - amount);
    cvlr_assert!(to_wallet_amount_post == to_wallet_amount_pre + amount);
}

pub fn process_transfer(
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> Result<(), ProgramError> {
    let token_program = &accounts[0];
    let from = &accounts[1];
    let to = &accounts[2];
    let authority = &accounts[3];
    let amount = u64::from_le_bytes(
        instruction_data[..8]
            .try_into()
            .expect("Invalid slice length"),
    );
    let instruction = transfer(
        token_program.key,
        from.key,
        to.key,
        authority.key,
        &[],
        amount,
    )?;
    let account_infos = vec![from.clone(), to.clone(), authority.clone()];
    cvlr_invoke_transfer(&instruction, &account_infos)?;
    Ok(())
}

pub fn rule_to_compile_mint_to() {
    let account_infos = super::cvlr_deserialize_nondet_accounts();
    let account_info_iter = &mut account_infos.iter();
    let token_program: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let from: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let to: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let _authority: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let amount: u64 = cvlr_nondet::nondet();
    let decimals: u8 = cvlr_nondet::nondet();
    let mut token_instruction_data = Vec::new();
    token_instruction_data.extend_from_slice(&amount.to_le_bytes());
    token_instruction_data.extend_from_slice(&decimals.to_le_bytes());
    cvlr_assume!(from.key != to.key);
    let from_wallet_amount_pre = spl_token_account_get_amount(from);
    let to_wallet_amount_pre = spl_token_account_get_amount(to);
    process_mint_to(&account_infos, &token_instruction_data).unwrap();
    let from_wallet_amount_post = spl_token_account_get_amount(from);
    let to_wallet_amount_post = spl_token_account_get_amount(to);
    cvlr_assert!(*token_program.key == spl_token::id());
    cvlr_assert!(from_wallet_amount_post == from_wallet_amount_pre - amount);
    cvlr_assert!(to_wallet_amount_post == to_wallet_amount_pre + amount);
}

pub fn process_mint_to(
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> Result<(), ProgramError> {
    let token_program = &accounts[0];
    let from = &accounts[1];
    let to = &accounts[2];
    let authority = &accounts[3];
    let amount = u64::from_le_bytes(
        instruction_data[..8]
            .try_into()
            .expect("Invalid slice length"),
    );
    let instruction = transfer(
        token_program.key,
        from.key,
        to.key,
        authority.key,
        &[],
        amount,
    )?;
    let account_infos = vec![from.clone(), to.clone(), authority.clone()];
    cvlr_invoke_mint_to(&instruction, &account_infos)?;
    Ok(())
}

pub fn rule_to_compile_burn() {
    let account_infos = super::cvlr_deserialize_nondet_accounts();
    let account_info_iter = &mut account_infos.iter();
    let token_program: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let from: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let to: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let _authority: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let amount: u64 = cvlr_nondet::nondet();
    let decimals: u8 = cvlr_nondet::nondet();
    let mut token_instruction_data = Vec::new();
    token_instruction_data.extend_from_slice(&amount.to_le_bytes());
    token_instruction_data.extend_from_slice(&decimals.to_le_bytes());
    cvlr_assume!(from.key != to.key);
    let from_wallet_amount_pre = spl_token_account_get_amount(from);
    let to_wallet_amount_pre = spl_token_account_get_amount(to);
    process_burn(&account_infos, &token_instruction_data).unwrap();
    let from_wallet_amount_post = spl_token_account_get_amount(from);
    let to_wallet_amount_post = spl_token_account_get_amount(to);
    cvlr_assert!(*token_program.key == spl_token::id());
    cvlr_assert!(from_wallet_amount_post == from_wallet_amount_pre - amount);
    cvlr_assert!(to_wallet_amount_post == to_wallet_amount_pre + amount);
}

pub fn process_burn(accounts: &[AccountInfo], instruction_data: &[u8]) -> Result<(), ProgramError> {
    let token_program = &accounts[0];
    let src = &accounts[1];
    let to = &accounts[2];
    let authority = &accounts[3];
    let amount = u64::from_le_bytes(
        instruction_data[..8]
            .try_into()
            .expect("Invalid slice length"),
    );
    let instruction = transfer(
        token_program.key,
        src.key,
        to.key,
        authority.key,
        &[],
        amount,
    )?;
    let account_infos = vec![src.clone(), to.clone(), authority.clone()];
    cvlr_invoke_burn(&instruction, &account_infos)?;
    Ok(())
}

pub fn rule_to_compile_close_account() {
    let account_infos = super::cvlr_deserialize_nondet_accounts();
    let account_info_iter = &mut account_infos.iter();
    let token_program: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let from: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let to: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let _authority: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let amount: u64 = cvlr_nondet::nondet();
    let decimals: u8 = cvlr_nondet::nondet();
    let mut token_instruction_data = Vec::new();
    token_instruction_data.extend_from_slice(&amount.to_le_bytes());
    token_instruction_data.extend_from_slice(&decimals.to_le_bytes());
    cvlr_assume!(from.key != to.key);
    let from_wallet_amount_pre = spl_token_account_get_amount(from);
    let to_wallet_amount_pre = spl_token_account_get_amount(to);
    process_close_account(&account_infos, &token_instruction_data).unwrap();
    let from_wallet_amount_post = spl_token_account_get_amount(from);
    let to_wallet_amount_post = spl_token_account_get_amount(to);
    cvlr_assert!(*token_program.key == spl_token::id());
    cvlr_assert!(from_wallet_amount_post == from_wallet_amount_pre - amount);
    cvlr_assert!(to_wallet_amount_post == to_wallet_amount_pre + amount);
}

pub fn process_close_account(
    accounts: &[AccountInfo],
    _instruction_data: &[u8],
) -> Result<(), ProgramError> {
    let token_program = &accounts[0];
    let src = &accounts[1];
    let to = &accounts[2];
    let authority = &accounts[3];
    let instruction = close_account(token_program.key, src.key, to.key, authority.key, &[])?;
    let account_infos = vec![src.clone(), to.clone(), authority.clone()];
    cvlr_invoke_close_account(&instruction, &account_infos)?;
    Ok(())
}

pub fn rule_to_compile_transfer_checked() {
    let account_infos = super::cvlr_deserialize_nondet_accounts();
    let account_info_iter = &mut account_infos.iter();
    let token_program: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let from: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let _mint: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let to: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let _authority: &AccountInfo = next_account_info(account_info_iter).unwrap();
    let amount: u64 = cvlr_nondet::nondet();
    let decimals: u8 = cvlr_nondet::nondet();
    let mut token_instruction_data = Vec::new();
    token_instruction_data.extend_from_slice(&amount.to_le_bytes());
    token_instruction_data.extend_from_slice(&decimals.to_le_bytes());
    cvlr_assume!(from.key != to.key);
    let from_wallet_amount_pre = spl_token_account_get_amount(from);
    let to_wallet_amount_pre = spl_token_account_get_amount(to);
    process_transfer_checked(&account_infos, &token_instruction_data).unwrap();
    let from_wallet_amount_post = spl_token_account_get_amount(from);
    let to_wallet_amount_post = spl_token_account_get_amount(to);
    cvlr_assert!(*token_program.key == spl_token::id());
    cvlr_assert!(from_wallet_amount_post == from_wallet_amount_pre - amount);
    cvlr_assert!(to_wallet_amount_post == to_wallet_amount_pre + amount);
}

pub fn process_transfer_checked(
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> Result<(), ProgramError> {
    let token_program = &accounts[0];
    let from = &accounts[1];
    let mint = &accounts[2];
    let to = &accounts[3];
    let authority = &accounts[4];
    let amount = u64::from_le_bytes(instruction_data[..8].try_into().unwrap());
    let decimals = u8::from_le_bytes(instruction_data[8..9].try_into().unwrap());
    let instruction = transfer_checked(
        token_program.key,
        from.key,
        mint.key,
        to.key,
        authority.key,
        &[],
        amount,
        decimals,
    )?;
    let account_infos = vec![from.clone(), mint.clone(), to.clone(), authority.clone()];
    cvlr_invoke_transfer_checked(&instruction, &account_infos)?;
    Ok(())
}
