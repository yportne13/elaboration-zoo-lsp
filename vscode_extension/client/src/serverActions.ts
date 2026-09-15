/* --------------------------------------------------------------------------------------------
 * Status-bar action picker for the TyportHDL language server.
 *
 * Shared by the WASM entry (`extension.ts`, used on web and on the desktop
 * WASM backend) and the desktop entry (`extension.desktop.ts`, CLI backend).
 * The picker switches the language server backend (WASM vs CLI); the
 * elaboration engine is no longer a user-facing choice — the desktop backends
 * run the L13 performance twin, while the WASM backend defaults to the
 * reference elaborator (see `UNSET_ENGINE`).  `readEngine` honors an explicit
 * `typort-hdl.cli-server.engine` setting as the escape hatch in both
 * directions, on the web host too.
 * ------------------------------------------------------------------------------------------ */

import { commands, ConfigurationTarget, QuickPickItem, QuickPickItemKind, window, workspace } from 'vscode';

/** Elaboration engine passed to the server as `TYPORT_LSP_ENGINE`. */
export type Engine = 'reference' | 'twin';
/** Language server backend the extension is running. */
export type Backend = 'wasm' | 'cli';

const SECTION = 'typort-hdl';
export const ENGINE_KEY = 'cli-server.engine';
export const BACKEND_KEY = 'lsp-mode';

/** Engine used when the setting has not been set explicitly. */
const UNSET_ENGINE: Record<Backend, Engine> = {
	// The CLI backend runs the L13 twin.  The web (wasm) backend defaults to
	// the reference elaborator: the twin's resident state needs ~1.2 GB of the
	// wasm module's hard 2 GiB linear-memory ceiling (the SharedArrayBuffer
	// maximum) for one proof-sized file, and a guest that cannot grow dies as a
	// `RuntimeError: unreachable` trap that the client never sees — the status
	// bar keeps claiming "running" while the server is gone.  The reference
	// path needs ~0.33 GB for the same file.  Opt back in per machine with
	// `typort-hdl.cli-server.engine = "twin"`.
	wasm: 'reference',
	cli: 'twin',
};

/**
 * The user-set value, ignoring the schema default. `get()` alone cannot be
 * used here: the schema default (`twin`, see package.json) would be
 * indistinguishable from an explicit choice.
 */
function explicitEngine(): string | undefined {
	const inspect = workspace.getConfiguration(SECTION).inspect<string>(ENGINE_KEY);
	return inspect?.workspaceFolderValue ?? inspect?.workspaceValue ?? inspect?.globalValue;
}

/** `twin` (the L13 performance elaborator) is the only value that opts in. */
export function readEngine(backend: Backend): Engine {
	const explicit = explicitEngine();
	if (explicit !== undefined) {
		return explicit.toLowerCase() === 'twin' ? 'twin' : 'reference';
	}
	return UNSET_ENGINE[backend];
}

export function readBackend(): Backend {
	const value = workspace.getConfiguration(SECTION).get<string>(BACKEND_KEY, 'wasm');
	return value.toLowerCase() === 'cli' ? 'cli' : 'wasm';
}

/**
 * Persist a setting where it is already overridden: a workspace-level value
 * would otherwise shadow a user-level write and the switch would look like a
 * no-op.
 */
async function writeSetting(key: string, value: string): Promise<void> {
	const config = workspace.getConfiguration(SECTION);
	const target = config.inspect(key)?.workspaceValue !== undefined
		? ConfigurationTarget.Workspace
		: ConfigurationTarget.Global;
	await config.update(key, value, target);
}

export interface ServerActionHost {
	/** Backend the running client was started with. */
	readonly backend: Backend;
	/** Engine the running client was started with. */
	readonly engine: Engine;
	/** Restart the client in place, re-reading settings. */
	restart(): Promise<void>;
	/** Reveal the language server log channel. */
	showLog(): void;
	/** Whether this host can spawn the external CLI server (desktop). */
	readonly canUseCli: boolean;
	/** Human-readable liveness of the running server, when known. */
	readonly liveness?: () => string;
}

type ActionItem = QuickPickItem & { action?: string; backend?: Backend; engine?: Engine };

function radio(selected: boolean, label: string): string {
	return `${selected ? '$(circle-filled)' : '$(circle-outline)'} ${label}`;
}

/** Builds the picker entries; exported for tests / callers that pre-filter. */
export function serverActionItems(host: ServerActionHost): ActionItem[] {
	const items: ActionItem[] = [];

	items.push(
		{ label: 'Elaboration engine', kind: QuickPickItemKind.Separator },
		{
			label: radio(host.engine === 'reference', 'Reference'),
			description: 'baseline elaborator; ~0.3 GB in the web host',
			engine: 'reference',
		},
		{
			label: radio(host.engine === 'twin', 'Twin (performance)'),
			description: 'faster per edit, ~2x memory (~1.2 GB in the web host)',
			engine: 'twin',
		},
	);

	if (host.liveness) {
		items.push(
			{ label: 'Status', kind: QuickPickItemKind.Separator },
			{ label: `$(pulse) Language server: ${host.liveness()}` },
		);
	}

	if (host.canUseCli) {
		items.push(
			{ label: 'Language server backend', kind: QuickPickItemKind.Separator },
			{
				label: radio(host.backend === 'wasm', 'WASM (built-in)'),
				description: 'bundled server.wasm; no external binary',
				backend: 'wasm',
			},
			{
				label: radio(host.backend === 'cli', 'CLI (external typort)'),
				description: 'spawns `typort lsp`',
				backend: 'cli',
			},
		);
	}

	items.push(
		{ label: '', kind: QuickPickItemKind.Separator },
		{ label: '$(debug-restart) Restart Language Server', action: 'restart' },
		{ label: '$(output) Show Log', action: 'log' },
	);
	return items;
}

/**
 * Switch the elaboration engine.  Both hosts re-read `typort-hdl.cli-server.engine`
 * when they (re)start, so this takes effect in place — no window reload.
 */
async function applyEngine(engine: Engine, host: ServerActionHost): Promise<void> {
	if (engine === host.engine) {
		return;
	}
	await writeSetting(ENGINE_KEY, engine);
	await host.restart();
	window.showInformationMessage(`TyportHDL: elaboration engine = ${engine}.`);
}

async function applyBackend(backend: Backend, host: ServerActionHost): Promise<void> {
	if (backend === host.backend) {
		return;
	}
	if (backend === 'cli' && !host.canUseCli) {
		window.showInformationMessage('The CLI backend is not available in this host.');
		return;
	}
	await writeSetting(BACKEND_KEY, backend);
	// The backend is chosen once at activation, so re-activate the extension.
	await commands.executeCommand('workbench.action.reloadWindow');
}

/** The status-bar item's command handler. */
export async function showServerActions(host: ServerActionHost): Promise<void> {
	const pick = await window.showQuickPick(serverActionItems(host), {
		placeHolder: 'Language Server Actions',
	});
	if (!pick) {
		return;
	}
	if (pick.engine) {
		await applyEngine(pick.engine, host);
	} else if (pick.backend) {
		await applyBackend(pick.backend, host);
	} else if (pick.action === 'restart') {
		await host.restart();
	} else if (pick.action === 'log') {
		host.showLog();
	}
}
