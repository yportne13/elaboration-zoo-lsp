/* --------------------------------------------------------------------------------------------
 * Status-bar action picker for the TyportHDL language server.
 *
 * Shared by the WASM entry (`extension.ts`, used on web and on the desktop
 * WASM backend) and the desktop entry (`extension.desktop.ts`, CLI backend).
 * The picker exposes the two elaboration backends and the two engines; the
 * engine only takes effect on the CLI backend, so selecting `twin` from a
 * WASM host first offers to move to the CLI backend.
 * ------------------------------------------------------------------------------------------ */

import { commands, ConfigurationTarget, QuickPickItem, QuickPickItemKind, window, workspace } from 'vscode';

/** Elaboration engine passed to the CLI server as `TYPORT_LSP_ENGINE`. */
export type Engine = 'reference' | 'twin';
/** Language server backend the extension is running. */
export type Backend = 'wasm' | 'cli';

const SECTION = 'typort-hdl';
export const ENGINE_KEY = 'cli-server.engine';
export const BACKEND_KEY = 'lsp-mode';

/** Engine used when the setting has not been set explicitly. */
const UNSET_ENGINE: Record<Backend, Engine> = {
	// The WASM backend is the out-of-the-box experience: default to the fast
	// L13 twin. The CLI backend is a power-user path and keeps the low-memory
	// reference engine unless the setting is set explicitly.
	wasm: 'twin',
	cli: 'reference',
};

/**
 * The user-set value, ignoring the schema default. `get()` alone cannot be
 * used here: the schema default (`twin`, see package.json) would be
 * indistinguishable from an explicit choice, and the CLI backend needs the
 * opposite fallback.
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
	/** Restart the client in place, re-reading settings. */
	restart(): Promise<void>;
	/** Reveal the language server log channel. */
	showLog(): void;
	/** Whether this host can spawn the external CLI server (desktop). */
	readonly canUseCli: boolean;
	/** Whether this host can run the twin engine at all. */
	readonly canUseTwin: boolean;
}

type ActionItem = QuickPickItem & { action?: string; engine?: Engine; backend?: Backend };

function radio(selected: boolean, label: string): string {
	return `${selected ? '$(circle-filled)' : '$(circle-outline)'} ${label}`;
}

/** Builds the picker entries; exported for tests / callers that pre-filter. */
export function serverActionItems(host: ServerActionHost): ActionItem[] {
	const items: ActionItem[] = [];

	if (host.canUseTwin) {
		const engine = readEngine(host.backend);
		items.push(
			{ label: 'Elaboration engine', kind: QuickPickItemKind.Separator },
			{
				label: radio(engine === 'reference', 'Reference'),
				description: 'baseline; lower memory',
				engine: 'reference',
			},
			{
				label: radio(engine === 'twin', 'Twin (performance)'),
				description: host.backend === 'cli'
					? '~3.8x faster per edit, ~2x memory'
					: '~3.8x faster per edit; raises the WASM memory ceiling',
				engine: 'twin',
			},
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

async function applyEngine(engine: Engine, host: ServerActionHost): Promise<void> {
	if (engine === readEngine(host.backend)) {
		return;
	}
	if (!host.canUseTwin) {
		window.showInformationMessage('The twin engine is not available in this host.');
		return;
	}
	// Both backends read the setting at spawn, so a restart applies it.
	await writeSetting(ENGINE_KEY, engine);
	await host.restart();
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
